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
    stage ('Build & Test') {
      parallel {
        // gcc builds
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
  echo "Step: Configure for '${tags}'"
  def ret = sh(returnStatus: true,
               script: """#!/bin/bash +ex
                          mkdir build || exit 1
                          cd build || exit 1
                          cmake -C ../cmake/jenkins.cmake -DCMAKE_BUILD_TYPE=$build_type -G "$generator" $cmake_opts .. || exit 1
                          cmake --build . || exit 1
                          exit 0""")
  if (ret) {
    echo "[!!!] Configure failed!"
    currentBuild.result = 'FAILURE'
    return
  }
  echo "Step: Build for '${tags}'"
  def ret = sh(returnStatus: true,
               script: """#!/bin/bash +ex
                          cd build || exit 1
                          cmake --build . || exit 1
                          exit 0""")
  if (ret) {
    echo "[!!!] Build failed!"
    currentBuild.result = 'FAILURE'
    return
  } else if (currentBuild.result != "FAILURE") {
    echo "SUCCESS"
  }
  echo "Step: Test for '${tags}'"
  def ret = sh(returnStatus: true,
               script: """#!/bin/bash +ex
                          declare -i RESULT=0
                          cd build || exit 1
                          if [ `uname` = "Darwin" ] ; then
                            export DYLD_LIBRARY_PATH="$PWD/build/lib"
                          elif [ `uname` = "FreeBSD" ] ; then
                            export LD_LIBRARY_PATH="$PWD/build/lib"
                          else
                            export LD_LIBRARY_PATH="$PWD/build/lib"
                            export ASAN_OPTIONS=detect_leaks=1
                          fi
                          RESULT=ctest --output-on-failure .
                          exit \$RESULT""")
  if (ret) {
    echo "[!!!] Test failed!"
    currentBuild.result = 'FAILURE'
    return
  }
  if (currentBuild.result != "FAILURE") {
    echo "SUCCESS"
    currentBuild.result = 'SUCCESS'
  }
}

def do_ms_stuff(tags,
                cmake_opts = "",
                build_type = "Debug",
                generator = "Visual Studio 15 2017",
                build_opts = "") {
  withEnv(['PATH=C:\\Windows\\System32;C:\\Program Files\\CMake\\bin;C:\\Program Files\\Git\\cmd']) {
    deleteDir()
    bat "echo \"Starting build with \'${tags}\'\""
    bat 'echo "Checkout"'
    // TODO: pull from mirror, not from GitHub, (RIOT fetch func?)
    checkout scm
    bat "echo \"Step: Configure for '${tags}'\""
    def ret = bat(returnStatus: true,
                  script: """cmake -E make_directory build
                             cd build
                             cmake -DCMAKE_BUILD_TYPE=${build_type} -G "${generator}" ${cmake_opts} ..
                             IF /I "%ERRORLEVEL%" NEQ "0" (
                               EXIT 1
                             )
                             EXIT 0""")
    if (ret) {
      echo "[!!!] Configure failed!"
      currentBuild.result = 'FAILURE'
      return
    }
    bat "echo \"Step: Build for '${tags}'\""
    def ret = bat(returnStatus: true,
                  script: """cd build
                             cmake --build .
                             IF /I "%ERRORLEVEL%" NEQ "0" (
                               EXIT 1
                             )
                             EXIT 0""")
    if (ret) {
      echo "[!!!] Build failed!"
      currentBuild.result = 'FAILURE'
      return
    }
    bat "echo \"Step: Test for '${tags}'\""
    def ret = bat(returnStatus: true,
                  script: """cd build
                             ctest --output-on-failure .
                             IF /I "%ERRORLEVEL%" NEQ "0" (
                               EXIT 1
                             )
                             EXIT 0""")
    if (ret) {
      echo "[!!!] Test failed!"
      currentBuild.result = 'FAILURE'
      return
    }
  }
}
