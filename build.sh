#!/bin/bash
cd Network_Security_Policy_Verification
export AFP=$(readlink -f "../isabelle_afp")

#echo "quick_and_dirty"
#-o quick_and_dirty

isabelle build -d "./" -b -o "document=pdf" -o "document_variants=document:outline=/proof,/ML" -vc Network_Security_Policy_Verification &&
  isabelle build -d "./" -b -v Network_Security_Policy_Verification_Examples
