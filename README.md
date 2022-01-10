# Formal Analysis of Non-Malleability for Commitments in EasyCrypt


Setup
-----

* For this project we used the developement version of EasyCrypt (1.0)
theorem prover with git-hash: 512f0f2bd8dc8c1132f3cd138a17d57d4db9c514

* EasyCrypt was configured with support from the following SMT solvers:
Why3@1.4.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.0

* to check the development run:
  
  $> cd DEVELOPMENT_FOLDER
  $> bash checkall


Contents
--------

* checkall - script for running the EasyCrypt proof-checker on the
  entire development.
  
* CNM_unsat.ec - definition of comparison-based non-malleability and
  the proof of its unsatisfiability.

  lemma cnm_unsat formalizes Thm. 1 from Sec. 2.1.

* NSNM_Definition.ec - novel definition of simulation-based
  non-malleability (for stateless and stateful commitment-schemes).

* NSNM_Pure_Binding.ec - novel sim-based non-mall. implies binding.

  lemma nsnm_pure_binding formalizes Lemma 1 from Sec. 3.1.

* NSNM_Pure_Hiding.ec - novel sim-based non-mall. implies hiding.

  lemma nsnm_pure_hiding formalizes Lemma 2 form Sec. 3.1.

* LRO.ec - implementation and properties of Lazy Random Oracle.

* NSNM_ROM_Construction.ec - implementation of commitment scheme using
  Lazy Random Oracle which satisfies novel sim-based non-mall.

  lemma nsnm_lro_sec formalizes Thm 2 from Sec. 3.2.

* NSNM_Related.ec - the proof that the novel definition of sim-based
  non-malelability is stronger that previous definitions by
  Crescenzo~et~al. and Arita.

  lemmas arita_to_nsnm and cresc_to_nsnm formalize Lemma 5 from Sec. 3.3.
  
* ConstComm.ec - the definition of a "constant"-commitment scheme and
  a proof that it is non-malleable with respect to the definition of
  Crescenzo~et~al. and malleable with respect to the definition by
  Arita.

  lemma cresc_const_comm formalizes Lemma 3 from Sec. 3.3.
  lemma arita_const_comm formalizes Lemma 4 from Sec. 3.3.


* WholeMsg.ec, D1D2.ec, HelperFuns.ec - auxiliary formalization of
  basic functions and definitions.


