#!/bin/bash
cd Network_Security_Policy_Verification
export AFP=$(readlink -f "../isabelle_afp")
isabelle build -d "./" -o document=pdf -o skip_proofs -vc Network_Security_Policy_Verification &&
  isabelle build -d "./" -vc Network_Security_Policy_Verification_Examples
