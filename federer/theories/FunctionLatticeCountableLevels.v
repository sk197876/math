(** Federer (1969), 2.5.14, p. 107: under a countable-base hypothesis, open
    sets are in F1. Supporting closure of level families from 2.5.3, p. 94. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelFamilyLaws
  CountableFamilySequence SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [function_lattice_sequence_strict_levels_union]: a sequence
    union of F0 sets belongs to F1, supporting Federer 2.5.14, p. 107 *)
Lemma function_lattice_sequence_strict_levels_union (R : realType) (X : Type)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) (V : nat -> set X) :
  L f -> (forall n, function_lattice_strict_levels L (V n)) ->
  function_lattice_increasing_levels L (\bigcup_n V n).
Proof.
move=> hf hV; exists (set_sequence_prefix V); split.
- elim=> [|n IH].
  + rewrite set_sequence_prefix_zero; exact: (@function_lattice_empty_strict_level R X L hL f hf).
  + rewrite set_sequence_prefix_succ; exact (@function_lattice_strict_levels_union R X L hL _ _ IH (hV n)).
- split; first by move=> n m; exact: set_sequence_prefix_mono.
  apply/seteqP; split.
  + move=> x [n _ hx]; exists n.+1=> //; exists n=> //; exact: ltnSn.
  + by move=> x [n _ [k hk hx]]; exists k.
Qed.

(** Source for [function_lattice_countable_strict_levels_union]:
    countable-family form of the supporting union assertion in Federer
    2.5.14, p. 107 The empty family is allowed because L is nonempty. *)
Lemma function_lattice_countable_strict_levels_union (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (f : X -> R) (C : set (set X)) :
  L f -> countable C -> (forall V, C V -> function_lattice_strict_levels L V) ->
  function_lattice_increasing_levels L (\bigcup_(V in C) V).
Proof.
move=> hf hc hC; have [G [hG he]] := @countable_family_as_sequence X [the choiceType of set X] C id hc.
rewrite -he; apply: (@function_lattice_sequence_strict_levels_union R X L hL f G hf)=> n.
case: (hG n)=> [->|[V [hV ->]]]; last exact: hC hV.
exact: (@function_lattice_empty_strict_level R X L hL f hf).
Qed.
