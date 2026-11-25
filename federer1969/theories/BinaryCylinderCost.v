(** Binary-cylinder costs for the local counterexample in Federer (1969),
    2.3.8, p. 78. Assign cost 2^(-length w) to the cylinder of w, and use
    the fixed-family construction from 2.10.1, p. 170. our binary coding
    supplies a self-contained witness. Source context:
    BinarySequenceCylinders.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [binary_cylinder_cost]: assigned cost for a
    prefix cylinder in the local Federer 2.3.8 example;
    input to the covering infimum of 2.10.1, p. 170. *)
Definition binary_cylinder_cost (R : realType) (w : seq bool) : \bar R :=
  (((2 : R)^+ (size w))^-1)%:E.

(** Source for [binary_cylinder_cost_positive]: every finite
    cylinder has positive assigned cost, supporting the counterexample
    for Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_cost_positive (R : realType) w : 0 < @binary_cylinder_cost R w.
Proof. by rewrite /binary_cylinder_cost lte_fin invr_gt0 exprn_gt0 // ltr0n. Qed.

(** Source for [binary_cylinder_cost_empty_word]: the whole
    binary product has assigned cost one, supporting the example
    for Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_cost_empty_word (R : realType) : @binary_cylinder_cost R [::] = 1.
Proof. by rewrite /binary_cylinder_cost /= expr0 invr1. Qed.

(** Source for [binary_cylinder_cost_refinement]: each refinement
    to length n has cost 2^(-n), and the total cost of
    the 2^(n-size w) extensions equals the original cost.
    This elementary equality supports Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_cost_refinement (R : realType) n w : (size w <= n)%N ->
  ((2 ^ (n-size w))%:R : R)%:E = ((2 : R)^+ n)%:E * @binary_cylinder_cost R w.
Proof.
move=> hw; rewrite /binary_cylinder_cost -EFinM natrX.
congr (_%:E); rewrite -{2}(subnK hw) exprD mulfK //.
by rewrite expf_neq0 // pnatr_eq0.
Qed.
