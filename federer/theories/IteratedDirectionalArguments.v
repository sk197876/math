(** Federer (1969), 3.1.11, p. 223: the reversal
    of the coordinate order in the formula for D_nu f. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import MultilinearSuccessorArguments MultilinearArgumentSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [iterated_directional_arguments]: the arguments
    (v_k,...,v_1) supplied to the kth differential when
    differentiating in the order D_v1 ... D_vk, Federer
    3.1.11, p. 223. *)
Fixpoint iterated_directional_arguments (K : fieldType) (X : lmodType K)
    (s : seq X) : {ffun 'I_(size s)->X} :=
  if s is v::s' then multilinear_successor_arguments (iterated_directional_arguments s') v
  else [ffun _ : 'I_0=>(0:X)].

(** Source for [iterated_directional_arguments_sequence]: the
    arguments of the recursive evaluation are exactly the reversed
    direction list in Federer 3.1.11, p. 223. *)
Lemma iterated_directional_arguments_sequence (K : fieldType) (X : lmodType K)
    (s : seq X) :
  multilinear_argument_sequence (iterated_directional_arguments s)=rev s.
Proof.
elim:s=>[|v s ih]; first by rewrite /iterated_directional_arguments
  /multilinear_argument_sequence enum_ord0.
by rewrite /= multilinear_argument_sequence_successor ih rev_cons cats1.
Qed.
