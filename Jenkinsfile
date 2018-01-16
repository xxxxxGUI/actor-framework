#!/usr/bin/env groovy

def gcc_builds = ["Linux && gcc4.8",
                  "Linux && gcc4.9",
                  "Linux && gcc5.1",
                  "Linux && gcc6.3",
                  "Linux && gcc7.2"]


pipeline {
  agent none

  parameters {
    string(name: 'sha1', defaultValue: '*/master', description: 'What branch / PR to build?``')
  }
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

// def build_stage(tags) {
//   return {
//     stage (tags) {
//       agent {
//         label tags
//       }
//       steps {
//         do_gcc_things("Linux && gcc4.9")
//       }
//     }
//   }
// }

def do_gcc_things(tags) {
  deleteDir()
  echo "building on nodes with tag ${tags}"
  echo "env.CHANGE_ID is ${env.CHANGE_ID}"
  echo "sha1 is ${params.sha1}"
  checkout([$class: 'GitSCM', branches: [[name: '${params.sha1}']], doGenerateSubmoduleConfigurations: false, extensions: [[$class: 'CloneOption', depth: 0, noTags: true, reference: '', shallow: false]], submoduleCfg: [], userRemoteConfigs: [[credentialsId: 'c3ecbe72-d64a-4d89-96a6-6d4cb76c43d1', refspec: '+refs/pull/*:refs/remotes/origin/pr/*', url: 'git@github.com:actor-framework/actor-framework.git']]])
  sh 'git branch'
  sh 'ls'
}
