# topoS
Verified synthesis and verification of network security policies.


Get Isabelle/HOL 2016 at
http://isabelle.in.tum.de/


The Network_Security_Policy_Verification is maintained in the AFP.
Get the latest stable version here:
http://afp.sourceforge.net/entries/Network_Security_Policy_Verification.shtml



This repo is where the development happens.

In theory files, identifiers are written with underscores.
Example: offending-flows-union-mono can be found with
find Network_Security_Policy_Verification/ -iname '*.thy' | xargs grep 'offending_flows_union_mono'

## Repo Overview

* Network_Security_Policy_Verification 
    
    Theory for reasoning about logical access control abstraction (security policy, who can communicate with whom?).
    All the the formal theory files for Isabelle/HOL.


* interface_abstraction
    
    A model of networks.


* isabelle_afp
    
    A snapshot of some afp entries to use this repository without external dependencies.


* scala_tool
    
    A stand-alone demonstration tool. It is quite unmaintained and out of sync with theory files!
    The Isabelle formalization now directly supports visualization.
    See Network_Security_Policy_Verification.thy for an example.
    If a new stand-alone tool is desired, we suggest to export the code directly from the Isabelle formalization.


### Academic Publications

  * Cornelius Diekmann, Andreas Korsten, and Georg Carle. Demonstrating topoS: Theorem-prover-based synthesis of secure network configurations. In 2nd International Workshop on Management of SDN and NFV Systems, manSDN/NFV, Barcelona, Spain, November 2015. [[preprint]](http://www.net.in.tum.de/fileadmin/bibtex/publications/papers/diekmann2015mansdnnfv.pdf)
  * Cornelius Diekmann, Stephan-A. Posselt, Heiko Niedermayer, Holger Kinkelin, Oliver Hanka, and Georg Carle. Verifying Security Policies using Host Attributes. In FORTE - 34th IFIP International Conference on Formal Techniques for Distributed Objects, Components and Systems, volume 8461, pages 133-148, Berlin, Germany, June 2014. Springer. [[preprint]](http://www.net.in.tum.de/fileadmin/bibtex/publications/papers/forte14_verifying_security_policies_using_host_attributes.pdf)
  * Cornelius Diekmann, Lars Hupel, and Georg Carle. Directed Security Policies: A Stateful Network Implementation. In Jun Pang and Yang Liu, editors, Engineering Safety and Security Systems, volume 150 of Electronic Proceedings in Theoretical Computer Science, pages 20-34, Singapore, May 2014. Open Publishing Association. [[paper]](http://rvg.web.cse.unsw.edu.au/eptcs/paper.cgi?ESSS2014.3)


