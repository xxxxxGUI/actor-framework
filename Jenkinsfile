#!/usr/bin/env groovy

def gcc_builds = ["Linux && gcc4.8",
                  "Linux && gcc4.9",
                  "Linux && gcc5.1",
                  "Linux && gcc6.3",
                  "Linux && gcc7.2"]


pipeline {
  agent none

  stages {
    stage ('Get') {
      steps {
        node ('master') {
          echo "Hello from master"
        }
      }
    }
    stage ('Build') {
      parallel {
        stage ("Linux && gcc4.8") {
          agent {
            label "Linux && gcc4.8"
          }
          steps {
            do_gcc_things("Linux && gcc4.8")
          }
        }
        stage ("Linux && gcc4.9") {
          agent {
            label "Linux && gcc4.9"
          }
          steps {
            do_gcc_things("Linux && gcc4.9")
          }
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

def do_gcc_things(tags) {
  deleteDir()
  echo "building on nodes with tag ${tags}"
  // checkout scm
  fetchPR(env.CHANGE_ID, "--depth=1", "")
  git branch
  git status
  sh 'ls'
}

def fetchPR(prNum, fetchArgs, extraRefSpec)
{
    sh """git init
    git remote add origin "https://github.com/actor-framework/actor-framework"
    echo "prNum is ${prNum}"
    ifconfig
    git fetch origin master
    git checkout master
    #for RETRIES in {1..3}; do
    #    timeout 30 git fetch -u -n ${fetchArgs} origin ${extraRefSpec} pull/${prNum}/merge:pull_${prNum} && break
    #done
    #[[ "\$RETRIES" -eq 3 ]] && exit 1
    #git checkout pull_${prNum}
    #git checkout master
    """
}
