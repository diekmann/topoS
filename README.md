# topoS
Verified synthesis and verification of network security policies.


Get Isabelle/HOL 2015 at
http://isabelle.in.tum.de/


The Network_Security_Policy_Verification is maintained in the AFP.
Get the latest stable version here:
http://afp.sourceforge.net/entries/Network_Security_Policy_Verification.shtml



This repo is where the development happens.

In theory files, identifiers are written with underscores.
Example: offending-flows-union-mono can be found with
find access_control_abstraction/thy/ -iname '*.thy' | xargs grep 'offending_flows_union_mono'

## Repo Overview

* Network_Security_Policy_Verification (former access_control_abstraction)
  Theory for reasoning about logical access control abstraction (security policy, who can communicate with whom?)
  All the the formal theory files for Isabelle/HOL

* interface_abstraction
  A model of networks

* isabelle_afp
  A snapshot of some afp entries to use this repository without external dependencies.

* scala_tool
  A stand-alone demonstration tool. It is quite unmaintained and out of sync with theory files!
  The Isabelle formalization now directly supports visualization.
  See Network_Security_Policy_Verification.thy for an example.
  If a new stand-alone tool is desired, we suggest to export the code directly from the Isabelle formalization.
