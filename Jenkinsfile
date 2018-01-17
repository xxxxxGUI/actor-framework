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
            echo "Hello from gcc 4.8"
            sh 'gcc -v'
            checkout scm
            sh 'git branch'
            sh 'ls'
            sh 'ifconfig'
          }
        }
        stage ("Linux && gcc4.9") {
          agent {
            label "Linux && gcc4.9"
          }
          steps {
            echo "Hello from gcc 4.9"
            sh 'gcc -v'
            checkout scm
            sh 'git branch'
            sh 'ls'
            sh 'ifconfig'
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
