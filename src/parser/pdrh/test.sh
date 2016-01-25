#!/usr/bin/env bash

((success=0))
((failure=0))
find $1 -name '*.drh' | while read line; do
                          ./pdrh $line
                          if [ "$?" == "0" ]; then
                          	((success++))
                          else
							((failure++))
                          fi
                          echo "success = " $success " failure = " $failure
                      done