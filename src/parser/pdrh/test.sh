#!/usr/bin/env bash

find $1 -name '*.drh' | while read line; do
                          ./pdrh $line
                      done