#!/usr/bin/env groovy

def clang_builds = ["Linux && clang && LeakSanitizer",
                    "macOS && clang"]
def gcc_builds = ["Linux && gcc4.8",
                  "Linux && gcc4.9",
                  "Linux && gcc5.1",
                  "Linux && gcc6.3",
                  "Linux && gcc7.2"]
def msvc_builds = ["msbuild"]

pipeline {
  agent none

  triggers {
    githubPullRequest {
      admins(['Neverlord', 'josephnoir', 'mavam'])
      orgWhitelist('actor-framework')
      cron('H/5 * * * *')
      triggerPhrase('.*test\\\W+this\\\W+please.*')
      // onlyTriggerPhrase()
      useGitHubHooks()
      // displayBuildErrorsOnDownstreamBuilds()
    }
  }

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
        stage ("Linux && gcc4.8") {
          agent { label "Linux && gcc4.8" }
          steps { do_stuff("Linux && gcc4.8") }
        }
        stage ("Linux && gcc4.9") {
          agent { label "Linux && gcc4.9" }
          steps { do_stuff("Linux && gcc4.9") }
        }
        stage ("macOS && clang") {
          agent { label "macOS && clang" }
          steps { do_stuff("macOS && clang") }
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

def do_stuff(tags,
             build_type = "Debug",
             generator = "Unix Makefiles",
             cmake_opts = "",
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
                          cmake -DCMAKE_BUILD_TYPE=$build_type -G $generator .. || RESULT=1
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
  // ctest .
}
