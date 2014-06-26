#!/bin/bash
cd Network_Security_Policy_Verification
export AFP=$(readlink -f "../isabelle_afp")
isabelle build -d "./" -v -l Network_Security_Policy_Verification &&
  isabelle build -d "./" -v -l Network_Security_Policy_Verification_Examples
