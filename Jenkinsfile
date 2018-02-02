#!/usr/bin/env groovy

def clang_builds = ["Linux && clang && LeakSanitizer",
                    "macOS && clang"]
def gcc_builds = ["Linux && gcc4.8",
                  "Linux && gcc4.9",
                  "Linux && gcc5.1",
                  "Linux && gcc6.3",
                  "Linux && gcc7.2"]
def msvc_builds = ["msbuild"]

def gcc_cmake_opts = "-DCAF_NO_PROTOBUF_EXAMPLES:BOOL=yes -DCAF_NO_QT_EXAMPLES:BOOL=yes -DCAF_MORE_WARNINGS:BOOL=yes -DCAF_ENABLE_ADDRESS_SANITIZER:BOOL=yes -DCAF_ENABLE_RUNTIME_CHECKS:BOOL=yes -DCAF_USE_ASIO:BOOL=yes -DCAF_NO_BENCHMARKS:BOOL=yes -DOPENSSL_ROOT_DIR=/usr/local/opt/openssl -DOPENSSL_INCLUDE_DIR=/usr/local/opt/openssl"

def clang_cmake_opts = "-DCAF_NO_PROTOBUF_EXAMPLES:BOOL=yes -DCAF_NO_QT_EXAMPLES:BOOL=yes -DCAF_MORE_WARNINGS:BOOL=yes -DCAF_ENABLE_ADDRESS_SANITIZER:BOOL=yes -DCAF_ENABLE_RUNTIME_CHECKS:BOOL=yes -DCAF_USE_ASIO:BOOL=yes -DCAF_NO_BENCHMARKS:BOOL=yes -DCAF_NO_OPENCL:BOOL=yes -DOPENSSL_ROOT_DIR=/usr/local/opt/openssl -DOPENSSL_INCLUDE_DIR=/usr/local/opt/openssl"

def msbuild_opts = "-DCAF_BUILD_STATIC_ONLY:BOOL=yes -DCAF_NO_BENCHMARKS:BOOL=yes -DCAF_NO_EXAMPLES:BOOL=yes -DCAF_NO_MEM_MANAGEMENT:BOOL=yes -DCAF_NO_OPENCL:BOOL=yes -DCAF_LOG_LEVEL:INT=0 -DCMAKE_CXX_FLAGS=\"/MP\""
// "-DCAF_BUILD_STATIC_ONLY:BOOL=yes -DCAF_NO_BENCHMARKS:BOOL=yes -DCAF_NO_OPENCL:BOOL=yes"

pipeline {
  agent none

  stages {
    stage ('Get') {
      steps {
        node ('master') {
          // TODO: pull github branch into mirror
          // TODO: set URL, refs, prNum?
          // TODO: maybe static tests?
          echo "Hello from master"
        }
      }
    }
    stage ('Build') {
      parallel {
        // GCC BUILDS
        stage ("Linux && gcc4.8") {
          agent { label "Linux && gcc4.8" }
          steps { do_unix_stuff("Linux && gcc4.8", gcc_cmake_opts) }
        }
        stage ("Linux && gcc4.9") {
          agent { label "Linux && gcc4.9" }
          steps { do_unix_stuff("Linux && gcc4.9", gcc_cmake_opts) }
        }
        stage ("Linux && gcc5.1") {
          agent { label "Linux && gcc5.1" }
          steps { do_unix_stuff("Linux && gcc5.1", gcc_cmake_opts) }
        }
        stage ("Linux && gcc6.3") {
          agent { label "Linux && gcc6.3" }
          steps { do_unix_stuff("Linux && gcc6.3", gcc_cmake_opts) }
        }
        stage ("Linux && gcc7.2") {
          agent { label "Linux && gcc7.2" }
          steps { do_unix_stuff("Linux && gcc7.2", gcc_cmake_opts) }
        }
        // clang builds
        stage ("macOS && clang") {
          agent { label "macOS && clang" }
          steps { do_unix_stuff("macOS && clang", clang_cmake_opts) }
        }
        stage('Linux && clang && LeakSanitizer') {
          agent { label "Linux && clang && LeakSanitizer" }
          steps { do_unix_stuff("Linux && clang && LeakSanitizer", clang_cmake_opts) }
        }
        // windows builds
        stage('msbuild') {
          agent { label "msbuild" }
          steps { do_ms_stuff("msbuild", msbuild_opts) }
        }
      }
    }
    stage ('Test') {
      steps {
        // execute unit tests?
        echo "Testing all the things"
      }
    }
  }
}

if (currentBuild.result == null) {
  currentBuild.result = 'SUCCESS'
}

def do_unix_stuff(tags,
                  cmake_opts = "",
                  build_type = "Debug",
                  generator = "Unix Makefiles",
                  build_opts = "") {
  deleteDir()
  echo "Starting build with '${tags}'"
  echo "Checkout"
  // TODO: pull from mirror, not from GitHub, (RIOT fetch func?)
  checkout scm
  echo "DEBUG INFO"
  sh 'git branch'
  echo "Configure"
  def ret = sh(returnStatus: true,
               script: """#!/bin/bash +ex
                          declare -i RESULT=0
                          mkdir build || RESULT=1
                          if ((\$RESULT)); then
                            exit \$RESULT
                          fi;
                          cd build || RESULT=1
                          if ((\$RESULT)); then
                            exit \$RESULT
                          fi;
                          echo "build_type: $build_type"
                          echo "generator: $generator"
                          cmake -C ../cmake/jenkins.cmake -DCMAKE_BUILD_TYPE=$build_type -G $generator $cmake_opts .. || RESULT=1
                          exit \$RESULT""")
  if (ret) {
    echo "FAILURE"
    currentBuild.result = 'FAILURE'
  } else {
    echo "SUCCESS"
  }
  echo "Build"
  // make -j 2 ${build_opts}
  echo "Test"
  // more shell scripts?
  // if [ `uname` = "Darwin" ] ; then
  //   export DYLD_LIBRARY_PATH="$PWD/build/lib"
  // elif [ `uname` = "FreeBSD" ] ; then
  //   export LD_LIBRARY_PATH="$PWD/build/lib"
  // else
  //   export LD_LIBRARY_PATH="$PWD/build/lib"
  //   export ASAN_OPTIONS=detect_leaks=1
  // fi
  // ctest --output-on-failure
}

def do_ms_stuff(tags,
                cmake_opts = "",
                build_type = "Debug",
                generator = "Visual Studio 15 2017",
                build_opts = "") {
  withEnv(['PATH=C:\\Windows\\System32;C:\\Program Files\\CMake\\bin;C:\\Program Files\\Git\\cmd']) {
    deleteDir()
    bat "echo \"Starting build with \'${tags}\'\""
    // bat 'echo "Checkout"'
    // TODO: pull from mirror, not from GitHub, (RIOT fetch func?)
    checkout scm
    // bat 'echo "DEBUG INFO"'
    bat 'git branch'
    // bat 'echo "Configure"'
    // bat 'echo "Not implemented on Windows ..."'
    // bat"""cmake -E make_directory build
    //      cd build
    //      echo "build_type: %build_type%"
    //      echo "generator: %generator%"
    //      cmake -DCMAKE_BUILD_TYPE=%build_type% -G %generator% %cmake_opts%
    //      cmake --build .
    //      """
    def ret = bat(returnStatus: true,
                  script: """SET RESULT=0
                             cmake -E make_directory build
                             cd build
                             echo "build_type: ${build_type}"
                             echo "generator: ${generator}"
                             cmake -DCMAKE_BUILD_TYPE=${build_type} -G "${generator}" ${cmake_opts}
                             ::cmake --build .
                             EXIT %RESULT%""")
    if (ret) {
      // echo "FAILURE"
      currentBuild.result = 'FAILURE'
    } //else {
    //   echo "SUCCESS"
    // }
    // bat 'echo "Build"'
    // make -j 2 ${build_opts}
    // bat 'echo "Test"'
    // ctest --output-on-failure
  }
}
