#!/bin/bash
cd Network_Security_Policy_Verification
export AFP=$(readlink -f "../isabelle_afp")

#echo "quick_and_dirty"
#-o quick_and_dirty

isabelle build -d "./" -o document=pdf -v Network_Security_Policy_Verification &&
  isabelle build -d "./" -v Network_Security_Policy_Verification_Examples
