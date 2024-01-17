# Qafny

Qafny is a project to utilize classical separation logic frameworks to verify quantum program properties.

## Overview

Many quantum programs are assured by formal verification, but such verification is usually laborious and time-consuming. This paper proposes Qafny, an automated proof system for verifying classical quantum hybrid algorithms. The core of Qafny is a quantum proof system, named the Qafny proof system. It views quantum operations as classical array aggregate operations with the guidance of a type system, which can be effectively verified in a classical separation logic framework. The proof system includes proof rules for proving properties of programs containing quantum conditionals, which is the first system that enables such proving power. We have shown the soundness and completeness of the Qafny proof system as well as the soundness of the proof system compilation from Qafny to Dafny. By using the Qafny implementation in Dafny, we enable the automated verification, with the saving of both human efforts and computer execution time, for many classical quantum hybrid algorithms, including GHZ, Shor’s algorithm, Grover’s algorithm, and quantum walk algorithm. In addition, quantum programs written in Qafny can be compiled to quantum circuits so that every verified quantum program can be run on a quantum machine.

## Setup

To compile Qafny, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.13**.

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "qnp"
opam switch create qnp 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We require Coq version >= 8.12. We have tested compilation with 8.12.2, 8.13.2, and 8.14.0.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running Qafny

Run `make` in the top-level directory to compile our Coq proofs. externals directory contains the coq files from SQIR and QWIRE that support the development of the Qafny proof.

## Directory Contents

* QafnySyntax.v - The LQafny language syntax.
* LocusDef.v - Locus and state syntax and equation rules.
* LocusType.v - The Qafny Type system.
* LocusSem.v - The Qafny language semantics.
* LocusTypeProof.v - The Qafny Type system Soundness Proof.
* LocusProof.v - The Qafny proof system and Soundness/Completeness Proof.
* QafnySQIR.v - The Qafny to SQIR compilation.


