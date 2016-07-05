#!/bin/bash

isabelle build -d ./thy -v -o document=pdf -b Network_Security_Policy_Verification
isabelle build -d ./thy -v -o document=pdf -b Network_Security_Policy_Verification_Examples
isabelle build -d ./thy -v -b Interface_Abstraction
