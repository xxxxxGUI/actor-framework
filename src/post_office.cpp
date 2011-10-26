#include <new>          // placement new
#include <ios>          // ios_base::failure
#include <list>         // std::list
#include <vector>       // std::vector
#include <cstring>      // strerror
#include <cstdint>      // std::uint32_t, std::uint64_t
#include <iostream>     // std::cout, std::endl
#include <exception>    // std::logic_error
#include <algorithm>    // std::find_if
#include <stdexcept>    // std::underflow_error
#include <sstream>

#include <cstdio>
#include <fcntl.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/types.h>

// used cppa classes
#include "cppa/to_string.hpp"
#include "cppa/deserializer.hpp"
#include "cppa/binary_deserializer.hpp"

// used cppa utility
#include "cppa/util/single_reader_queue.hpp"

// used cppa details
#include "cppa/detail/thread.hpp"
#include "cppa/detail/buffer.hpp"
#include "cppa/detail/mailman.hpp"
#include "cppa/detail/post_office.hpp"
#include "cppa/detail/native_socket.hpp"
#include "cppa/detail/network_manager.hpp"
#include "cppa/detail/post_office_msg.hpp"
#include "cppa/detail/singleton_manager.hpp"
#include "cppa/detail/actor_proxy_cache.hpp"

//#define DEBUG(arg) std::cout << arg << std::endl
#define DEBUG(unused) ((void) 0)

namespace cppa { namespace detail { namespace {

// allocate in 1KB chunks (minimize reallocations)
constexpr size_t s_chunk_size = 1024;

// allow up to 1MB per buffer
constexpr size_t s_max_buffer_size = (1024 * 1024);

static_assert((s_max_buffer_size % s_chunk_size) == 0,
              "max_buffer_size is not a multiple of chunk_size");

static_assert(sizeof(native_socket_t) == sizeof(std::uint32_t),
              "sizeof(native_socket_t) != sizeof(std::uint32_t)");

constexpr int s_rdflag = MSG_DONTWAIT;

} } } // namespace cppa::detail::<anonmyous>

namespace cppa { namespace detail {

util::single_reader_queue<mailman_job>& mailman_queue()
{
    return singleton_manager::get_network_manager()->mailman_queue();
}

} } // namespace cppa::detail

namespace cppa { namespace detail { namespace {

class post_office_worker
{

    size_t m_rc;
    native_socket_t m_parent;

    post_office_worker(const post_office_worker&) = delete;
    post_office_worker& operator=(const post_office_worker&) = delete;

 protected:

    native_socket_t m_socket;

    // caches process_information::get()
    process_information_ptr m_pself;

    post_office_worker(native_socket_t fd, native_socket_t parent_fd = -1)
        : m_rc((parent_fd != -1) ? 1 : 0)
        , m_parent(parent_fd)
        , m_socket(fd)
        , m_pself(process_information::get())
    {
    }

    post_office_worker(post_office_worker&& other)
        : m_rc(other.m_rc)
        , m_parent(other.m_parent)
        , m_socket(other.m_socket)
        , m_pself(process_information::get())
    {
        other.m_rc = 0;
        other.m_socket = -1;
        other.m_parent = -1;
    }

 public:

    inline size_t ref_count() const
    {
        return m_rc;
    }

    inline void inc_ref_count()
    {
        ++m_rc;
    }

    inline size_t dec_ref_count()
    {
        if (m_rc == 0)
        {
            throw std::underflow_error("post_office_worker::dec_ref_count()");
        }
        return --m_rc;
    }

    inline native_socket_t get_socket()
    {
        return m_socket;
    }

    inline bool has_parent() const
    {
        return m_parent != -1;
    }

    inline native_socket_t parent() const
    {
        return m_parent;
    }

    // @returnss new reference count
    size_t parent_exited(native_socket_t parent_socket)
    {
        if (has_parent() && parent() == parent_socket)
        {
            m_parent = -1;
            return dec_ref_count();
        }
        return ref_count();
    }

    virtual ~post_office_worker()
    {
        if (m_socket != -1)
        {
            closesocket(m_socket);
        }
    }

};

class po_peer : public post_office_worker
{

    typedef post_office_worker super;

    enum state
    {
        // connection just established; waiting for process information
        wait_for_process_info,
        // wait for the size of the next message
        wait_for_msg_size,
        // currently reading a message
        read_message
    };

    state m_state;
    process_information_ptr m_peer;
    std::unique_ptr<attachable> m_observer;
    buffer<s_chunk_size, s_max_buffer_size> m_rdbuf;
    std::list<actor_proxy_ptr> m_children;

    const uniform_type_info* m_meta_msg;

 public:

    explicit po_peer(post_office_msg::add_peer& from)
        : super(from.sockfd)
        , m_state(wait_for_msg_size)
        , m_peer(std::move(from.peer))
        , m_observer(std::move(from.attachable_ptr))
        , m_meta_msg(uniform_typeid<message>())
    {
    }

    explicit po_peer(native_socket_t sockfd, native_socket_t parent_socket)
        : super(sockfd, parent_socket)
        , m_state(wait_for_process_info)
        , m_meta_msg(uniform_typeid<message>())
    {
        m_rdbuf.reset(  sizeof(std::uint32_t)
                      + process_information::node_id_size);
    }

    po_peer(po_peer&& other)
        : super(std::move(other))
        , m_state(other.m_state)
        , m_peer(std::move(other.m_peer))
        , m_observer(std::move(other.m_observer))
        , m_rdbuf(std::move(other.m_rdbuf))
        , m_children(std::move(other.m_children))
        , m_meta_msg(uniform_typeid<message>())
    {
    }

    void add_child(const actor_proxy_ptr& pptr)
    {
        m_children.push_back(pptr);
    }

    ~po_peer()
    {
        if (!m_children.empty())
        {
            for (actor_proxy_ptr& pptr : m_children)
            {
                pptr->enqueue(message(nullptr, nullptr, atom(":KillProxy"),
                                      exit_reason::remote_link_unreachable));
            }
        }
    }

    // @returnss false if an error occured; otherwise true
    bool read_and_continue()
    {
        switch (m_state)
        {
            case wait_for_process_info:
            {
                if (!m_rdbuf.append_from(m_socket, s_rdflag)) return false;
                if (m_rdbuf.ready() == false)
                {
                    break;
                }
                else
                {
                    std::uint32_t process_id;
                    memcpy(&process_id, m_rdbuf.data(), sizeof(std::uint32_t));
                    process_information::node_id_type node_id;
                    memcpy(node_id.data(),
                           m_rdbuf.data() + sizeof(std::uint32_t),
                           process_information::node_id_size);
                    m_peer.reset(new process_information(process_id, node_id));
                    // inform mailman about new peer
                    mailman_queue().push_back(new mailman_job(m_socket,
                                                              m_peer));
                    m_rdbuf.reset();
                    m_state = wait_for_msg_size;
                    DEBUG("pinfo read: "
                          << m_peer->process_id
                          << "@"
                          << to_string(m_peer->node_id));
                    // fall through and try to read more from socket
                }
            }
            case wait_for_msg_size:
            {
                if (m_rdbuf.final_size() != sizeof(std::uint32_t))
                {
                    m_rdbuf.reset(sizeof(std::uint32_t));
                }
                if (!m_rdbuf.append_from(m_socket, s_rdflag)) return false;
                if (m_rdbuf.ready() == false)
                {
                    break;
                }
                else
                {
                    // read and set message size
                    std::uint32_t msg_size;
                    memcpy(&msg_size, m_rdbuf.data(), sizeof(std::uint32_t));
                    m_rdbuf.reset(msg_size);
                    m_state = read_message;
                    // fall through and try to read more from socket
                }
            }
            case read_message:
            {
                if (!m_rdbuf.append_from(m_socket, s_rdflag))
                {
                    // could not read from socket
                    return false;
                }
                if (m_rdbuf.ready() == false)
                {
                    // wait for new data
                    break;
                }
                message msg;
                binary_deserializer bd(m_rdbuf.data(), m_rdbuf.size());
                try
                {
                    m_meta_msg->deserialize(&msg, &bd);
                }
                catch (std::exception& e)
                {
                    // unable to deserialize message (format error)
                    DEBUG(to_uniform_name(typeid(e)) << ": " << e.what());
                    return false;
                }
                auto& content = msg.content();
                if (   content.size() == 1
                    && content.utype_info_at(0) == typeid(atom_value)
                    && *reinterpret_cast<const atom_value*>(content.at(0))
                       == atom(":Monitor"))
                {
                    actor_ptr sender = msg.sender();
                    if (sender->parent_process() == *process_information::get())
                    {
                        //cout << pinfo << " ':Monitor'; actor id = "
                        //     << sender->id() << endl;
                        // local actor?
                        // this message was send from a proxy
                        sender->attach_functor([=](std::uint32_t reason)
                        {
                            message msg(sender, sender,
                                        atom(":KillProxy"), reason);
                            auto mjob = new detail::mailman_job(m_peer, msg);
                            detail::mailman_queue().push_back(mjob);
                        });
                    }
                    else
                    {
                        DEBUG(":Monitor received for an remote actor");
                    }
                }
                else
                {
                    DEBUG("<-- " << to_string(msg));
                    auto r = msg.receiver();
                    if (r) r->enqueue(msg);
                }
                m_rdbuf.reset();
                m_state = wait_for_msg_size;
                break;
            }
            default:
            {
                throw std::logic_error("illegal state");
            }
        }
        return true;
    }

};

class po_doorman : public post_office_worker
{

    typedef post_office_worker super;

    // server socket
    actor_ptr published_actor;

    std::list<po_peer>* m_peers;

 public:

    explicit po_doorman(post_office_msg::add_server_socket& assm,
                        std::list<po_peer>* peers)
        : super(assm.server_sockfd)
        , published_actor(assm.published_actor)
        , m_peers(peers)
    {
    }

    po_doorman(po_doorman&& other)
        : super(std::move(other))
        , published_actor(std::move(other.published_actor))
        , m_peers(other.m_peers)
    {
    }

    // @returnss false if an error occured; otherwise true
    bool read_and_continue()
    {
        sockaddr addr;
        socklen_t addrlen;
        memset(&addr, 0, sizeof(addr));
        memset(&addrlen, 0, sizeof(addrlen));
        auto sfd = ::accept(m_socket, &addr, &addrlen);
        if (sfd < 0)
        {
            switch (errno)
            {
                case EAGAIN:
#               if EAGAIN != EWOULDBLOCK
                case EWOULDBLOCK:
#               endif
                {
                    // just try again
                    return true;
                }
                default: return false;
            }
        }
        auto id = published_actor->id();
        std::uint32_t process_id = m_pself->process_id();
        ::send(sfd, &id, sizeof(std::uint32_t), 0);
        ::send(sfd, &process_id, sizeof(std::uint32_t), 0);
        ::send(sfd, m_pself->node_id().data(), m_pself->node_id().size(), 0);
        m_peers->push_back(po_peer(sfd, m_socket));
        DEBUG("socket accepted; published actor: " << id);
        return true;
    }

};

// starts and stops mailman_loop
struct mailman_worker
{
    thread m_thread;
    mailman_worker() : m_thread(mailman_loop)
    {
    }
    ~mailman_worker()
    {
        mailman_queue().push_back(mailman_job::kill_job());
        m_thread.join();
    }
};

} } } // namespace cppa::detail::<anonmyous>

namespace cppa { namespace detail {

void post_office_loop(int pipe_read_handle, int pipe_write_handle)
{
    mailman_worker mworker;
    // map of all published actors (actor_id => list<doorman>)
    std::map<std::uint32_t, std::list<po_doorman> > doormen;
    // list of all connected peers
    std::list<po_peer> peers;
    // readset for select()
    fd_set readset;
    // maximum number of all socket descriptors
    int maxfd = 0;
    // initialize variables
    FD_ZERO(&readset);
    maxfd = pipe_read_handle;
    FD_SET(pipe_read_handle, &readset);
    // keeps track about what peer we are iterating at this time
    po_peer* selected_peer = nullptr;
    // thread id of post_office
    auto thread_id = this_thread::get_id();
    // if an actor calls its quit() handler in this thread,
    // we 'catch' the released socket here
    std::vector<native_socket_t> released_socks;
    auto& msg_queue = singleton_manager::get_network_manager()->post_office_queue();
    // functor that releases a socket descriptor
    // returns true if an element was removed from peers
    auto release_socket = [&](native_socket_t sockfd)
    {
        auto end = peers.end();
        auto i = std::find_if(peers.begin(), end, [sockfd](po_peer& pp) -> bool
        {
            return pp.get_socket() == sockfd;
        });
        if (i != end && i->dec_ref_count() == 0) peers.erase(i);
    };
    // initialize proxy cache
    get_actor_proxy_cache().set_callback([&](actor_proxy_ptr& pptr)
    {
        pptr->enqueue(message(pptr, nullptr, atom(":Monitor")));
        if (selected_peer == nullptr)
        {
            throw std::logic_error("selected_peer == nullptr");
        }
        selected_peer->add_child(pptr);
        selected_peer->inc_ref_count();
        auto msock = selected_peer->get_socket();
        pptr->attach_functor([msock, thread_id,
                              &released_socks,
                              pipe_write_handle] (std::uint32_t)
        {
            if (this_thread::get_id() == thread_id)
            {
                released_socks.push_back(msock);
            }
            else
            {
                pipe_msg msg = { dec_socket_ref_event,
                                 static_cast<std::uint32_t>(msock) };
                write(pipe_write_handle, msg, pipe_msg_size);
            }
        });
    });
    for (;;)
    {
        if (select(maxfd + 1, &readset, nullptr, nullptr, nullptr) < 0)
        {
            // must not happen
            perror("select()");
            exit(3);
        }
        // iterate over all peers and remove peers on error
        peers.remove_if([&](po_peer& peer) -> bool
        {
            if (FD_ISSET(peer.get_socket(), &readset))
            {
                selected_peer = &peer;
                return peer.read_and_continue() == false;
            }
            return false;
        });
        selected_peer = nullptr;
        // iterate over all doormen (accept new connections)
        for (auto& kvp : doormen)
        {
            // iterate over all doormen and remove doormen on error
            kvp.second.remove_if([&](po_doorman& doorman) -> bool
            {
                return    FD_ISSET(doorman.get_socket(), &readset)
                       && doorman.read_and_continue() == false;
            });
        }
        // read events from pipe
        if (FD_ISSET(pipe_read_handle, &readset))
        {
            pipe_msg pmsg;
            //memcpy(pmsg, pipe_msg_buf.data(), pipe_msg_buf.size());
            //pipe_msg_buf.clear();
            ::read(pipe_read_handle, &pmsg, pipe_msg_size);
            switch (pmsg[0])
            {
                case rd_queue_event:
                {
                    DEBUG("rd_queue_event");
                    post_office_msg* pom = msg_queue.pop();
                    if (pom->is_add_peer_msg())
                    {
                        //DEBUG("pom->is_add_peer_msg()");
                        auto& apm = pom->as_add_peer_msg();
                        actor_proxy_ptr pptr = apm.first_peer_actor;
                        po_peer pd(apm);
                        selected_peer = &pd;
                        if (pptr)
                        {
                            DEBUG("proxy added via post_office_msg");
                            get_actor_proxy_cache().add(pptr);
                        }
                        selected_peer = nullptr;
                        peers.push_back(std::move(pd));
                        DEBUG("new peer (remote_actor)");
                    }
                    else
                    {
                        //DEBUG("pom->is_add_peer_msg() == false");
                        auto& assm = pom->as_add_server_socket_msg();
                        auto& pactor = assm.published_actor;
                        if (pactor)
                        {
                            auto actor_id = pactor->id();
                            auto callback = [actor_id](std::uint32_t)
                            {
                                DEBUG("call post_office_unpublish() ...");
                                post_office_unpublish(actor_id);
                            };
                            if (pactor->attach_functor(std::move(callback)))
                            {
                                auto& dm = doormen[actor_id];
                                dm.push_back(po_doorman(assm, &peers));
                                DEBUG("new doorman");
                            }
                        }
                        else
                        {
                            DEBUG("nullptr published");
                        }
                    }
                    delete pom;
                    break;
                }
                case unpublish_actor_event:
                {
                    DEBUG("unpublish_actor_event");
                    auto kvp = doormen.find(pmsg[1]);
                    if (kvp != doormen.end())
                    {
                        // decrease ref count of all children of this doorman
                        for (po_doorman& dm : kvp->second)
                        {
                            auto parent_fd = dm.get_socket();
                            peers.remove_if([parent_fd](po_peer& ppeer) -> bool
                            {
                                return ppeer.parent_exited(parent_fd) == 0;
                            });
                        }
                        doormen.erase(kvp);
                    }
                    break;
                }
                case dec_socket_ref_event:
                {
                    release_socket(static_cast<native_socket_t>(pmsg[1]));
                    break;
                }
                case close_socket_event:
                {
                    auto sockfd = static_cast<native_socket_t>(pmsg[1]);
                    auto end = peers.end();
                    auto i = std::find_if(peers.begin(), end,
                                          [sockfd](po_peer& peer) -> bool
                    {
                        return peer.get_socket() == sockfd;
                    });
                    if (i != end) peers.erase(i);
                    break;
                }
                case shutdown_event:
                {
                    // goodbye
                    return;
                }
                default:
                {
                    std::ostringstream oss;
                    oss << "unexpected event type: " << pmsg[0];
                    throw std::logic_error(oss.str());
                }
            }
        }
        if (released_socks.empty() == false)
        {
            for (native_socket_t sockfd : released_socks)
            {
                release_socket(sockfd);
            }
            released_socks.clear();
        }
        // recalculate readset
        FD_ZERO(&readset);
        FD_SET(pipe_read_handle, &readset);
        maxfd = pipe_read_handle;
        for (po_peer& pd : peers)
        {
            auto fd = pd.get_socket();
            if (fd > maxfd) maxfd = fd;
            FD_SET(fd, &readset);
        }
        // iterate over key (actor id) value (doormen) pairs
        for (auto& kvp : doormen)
        {
            // iterate over values (doormen)
            for (auto& dm : kvp.second)
            {
                auto fd = dm.get_socket();
                if (fd > maxfd) maxfd = fd;
                FD_SET(fd, &readset);
            }
        }
    }
}

void post_office_add_peer(native_socket_t a0,
                          const process_information_ptr& a1,
                          const actor_proxy_ptr& a2,
                          std::unique_ptr<attachable>&& a3)
{
    auto nm = singleton_manager::get_network_manager();
    nm->post_office_queue().push_back(new post_office_msg(a0, a1, a2,
                                                          std::move(a3)));
    pipe_msg msg = { rd_queue_event, 0 };
    write(nm->write_handle(), msg, pipe_msg_size);
}

void post_office_publish(native_socket_t server_socket,
                         const actor_ptr& published_actor)
{
    DEBUG("post_office_publish(" << published_actor->id() << ")");
    auto nm = singleton_manager::get_network_manager();
    nm->post_office_queue().push_back(new post_office_msg(server_socket,
                                                          published_actor));
    pipe_msg msg = { rd_queue_event, 0 };
    write(nm->write_handle(), msg, pipe_msg_size);
}

void post_office_unpublish(std::uint32_t actor_id)
{
    DEBUG("post_office_unpublish(" << actor_id << ")");
    auto nm = singleton_manager::get_network_manager();
    pipe_msg msg = { unpublish_actor_event, actor_id };
    write(nm->write_handle(), msg, pipe_msg_size);
}

void post_office_close_socket(native_socket_t sfd)
{
    auto nm = singleton_manager::get_network_manager();
    pipe_msg msg = { close_socket_event, static_cast<std::uint32_t>(sfd) };
    write(nm->write_handle(), msg, pipe_msg_size);
}

} } // namespace cppa::detail
