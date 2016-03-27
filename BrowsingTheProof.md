#How to Browse the Proof Scripts

# Introduction #

There are two ways to browse.
  * ... definitions ... statements of theorems ...
  * ... intermediate proof states ...

As of 2007 June 14 you will need to jump through hoops to do the latter.
This process will be simplified as summer progresses.

# Prerequisites #
  * You will need to _recompile_ Coq to incorporate **SSReflect** (which is not yet publicly available) since the proofs use a more concise tactic     language than standard Coq
  * You may need Objective Caml, version 3.06 or later
  * You may need to _install_ a development release of Proof General.    Version 3.7pre070610 is known to work.


# SSReflect #
This is not yet publicly available.
But, if you've already got a copy, then ...
  1. Make sure that you do not have any environnement variable named  COQLIB or  COQBIN.
  1. Download the sources of the 8.1 version of Coq from http://coq.inria.fr/distrib-eng.html. The coq-8.1.tar.gz archive is recommended.
  1. Unpack the archive. This results in creating a directory called coq-8.1.
  1. In this directory do
    1. ./configure -opt -local
    1. make world
    * If you get an error message complaining about  coqide,skip it, you still have succeeded in compiling all what is  necessary  for ssreflect.
  1. In the .../coq-8.1/bin directory, you should have a coqtop file,  which  is the Coq toplevel.
  1. Set an environment variable COQTOP and a variable COQLIB both to       .../coq-8.1/, and an environment variable COQBIN to .../coq-8.1/bin. Add .../coq-8.1/bin to your PATH variable.
  1. Copy trunk/ssreflect/ssreflect\_81/ssreflect.ml4 file in the .../coq-8.1 directory (where trunk is the root directory of the not-yet-available code)
  1. Back in the directory .../coq-8.1, build the ssreflect toplevel:
    1. make ssreflect.cmx
      * Note for Mac OS users on a PowerPC: If you did not include the "-opt" argument to /configure, the do "make OCAMLOPT=ocamlopt.opt ssreflect.cmx" now. Otherwise you may encounter a "stack overflow" error message.
    1. coqmktop -opt -o ssrcoq ssreflect.cmx
      * If the system complains about a missing gramlib.cmxa, find the place  where  this camlp4 library is installed (typing for example **locate   gramlib.cmxa**),  and try again the command :
        1. coqmktop -opt -R /the/address/of/the/rep/where/gramlib/is/ -o ssrcoq
        1. ssreflect.cmx

# Proof General #

Download the sources from http://proofgeneral.inf.ed.ac.uk/develdownload.html

  1. In .xemacs/init.el add the line (load-file ".../ProofGeneral/generic/proof-site.el")
  1. et cetera ....