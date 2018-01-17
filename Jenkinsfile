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
        stage ("Linux && gcc4.8 --> master") {
          agent {
            label "Linux && gcc4.8"
          }
          when {
            branch 'master'
          }
          steps {
            echo "env.BRANCH_NAME is ${env.BRANCH_NAME}"
            checkout_master("Linux && gcc4.8")
          }
        }
        stage ("Linux && gcc4.8 --> pr") {
          agent {
            label "Linux && gcc4.8"
          }
          when {
            not {
              branch 'master'
            }
          }
          steps {
            echo "env.BRANCH_NAME is ${env.BRANCH_NAME}"
            checkout_pr("Linux && gcc4.8")
          }
        }
        stage ("Linux && gcc4.9") {
          agent {
            label "Linux && gcc4.9"
          }
          // if (env.BRANCH_NAME == 'master') {
          //   checkout_master("Linux && gcc4.9")
          // } else {
          //   checkout_pr("Linux && gcc4.9")
          // }
          when {
            branch 'master'
          }
          steps {
            checkout_master("Linux && gcc4.9")
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

def checkout_master(tags) {
  deleteDir()
  echo "building master on nodes with tag ${tags}"
  checkout([$class: 'GitSCM', branches: [[name: '*/master']], doGenerateSubmoduleConfigurations: false, extensions: [[$class: 'CloneOption', depth: 0, noTags: true, reference: '', shallow: false]], submoduleCfg: [], userRemoteConfigs: [[credentialsId: 'c3ecbe72-d64a-4d89-96a6-6d4cb76c43d1', url: 'git@github.com:actor-framework/actor-framework.git']]])
  sh 'git branch'
  sh 'ls'
}

def checkout_pr(tags) {
  deleteDir()
  echo "building PR on nodes with tag ${tags}"
  echo "sha1 is ${params.sha1}"
  checkout([$class: 'GitSCM', branches: [[name: '${sha1}']], doGenerateSubmoduleConfigurations: false, extensions: [[$class: 'CloneOption', depth: 0, noTags: true, reference: '', shallow: false]], submoduleCfg: [], userRemoteConfigs: [[credentialsId: 'c3ecbe72-d64a-4d89-96a6-6d4cb76c43d1', refspec: '+refs/pull/*:refs/remotes/origin/pr/*', url: 'git@github.com:actor-framework/actor-framework.git']]])
  sh 'git branch'
  sh 'ls'
}

def do_gcc_things(tags) {
  deleteDir()
  echo "building on nodes with tag ${tags}"
  echo "env.CHANGE_ID is ${env.CHANGE_ID}"
  echo "sha1 is ${params.sha1}"
  checkout([$class: 'GitSCM', branches: [[name: '${params.sha1}']], doGenerateSubmoduleConfigurations: false, extensions: [[$class: 'CloneOption', depth: 0, noTags: true, reference: '', shallow: false]], submoduleCfg: [], userRemoteConfigs: [[credentialsId: 'c3ecbe72-d64a-4d89-96a6-6d4cb76c43d1', refspec: '+refs/pull/*:refs/remotes/origin/pr/*', url: 'git@github.com:actor-framework/actor-framework.git']]])
  sh 'git branch'
  sh 'ls'
}
