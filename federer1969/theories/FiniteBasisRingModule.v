(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328,
    and (8), p. 329. Connect the existing Chapter 1 finite basis
    to the independently specified finite-generation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import LinearBasis RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_basis_ring_module]: supporting finite-module
    connection for Federer 3.4.8(8), p. 329 and the auxiliary argument
    in (5), p. 328. A finite field basis generates the whole original
    module in the independent least-submodule sense. *)
Theorem finite_basis_ring_module (K:fieldType) (V:lmodType K) n
    (e:'I_n->V):is_basis e ->
  is_finitely_generated_ring_submodule (setT:set V).
Proof.
move=>hE;exists (map e (enum 'I_n));constructor.
- by constructor.
- by move=>v _.
- move=>N hN hGenerators x _.
  apply:(@basis_induction K [the choiceType of 'I_n] V e hE N _ _ _ _ x).
  + exact:ring_submodule_zero hN.
  + exact:ring_submodule_add hN.
  + exact:ring_submodule_scale hN.
  + move=>i;apply:hGenerators;apply/mapP;exists i=>//;exact:mem_enum.
Qed.
