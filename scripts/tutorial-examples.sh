#!/bin/bash

examples=(
  "examples/basic-hash.sp"
  "examples/private-authentication.sp"
  "examples/stateful/toy-counter.sp"
  "examples/stateful/running-ex-secrecy.sp"
  "examples/stateful/yubikey.sp"
  "examples/signed-ddh-P.sp"
  "examples/signed-ddh-S.sp"
)

for ex in ${examples[*]}; do 
  echo "Generating html file for $ex"
  ${PWD}/squirrel ${PWD}/${ex} --html ${PWD}/html_output/page.html 
done