(** Constant-value calculation for the domain-sensitive covering limit in
    Federer (1969), 2.8.16, p. 151, supporting the partial-quotient
    counterexample to 2.10.17(2), p. 179. Fineness is required on the domain
    of the partial function. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP CoveringRelationUP CoveringRelationFineness CoveringRelationLimits
  ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_upper_limit_constant_fine_domain]:
    supporting computation of the partial density limit
    in the local counterexample to 2.10.17(2),
    p. 179. All defined related values equal c,
    and their domain is fine, so the upper limit is c.
    This expands 2.8.16, p. 151, without assigning
    values outside the function's domain. *)
Lemma covering_upper_limit_constant_fine_domain (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) (x : X) c :
  covering_relation_fine_at (fun x S => C x S /\ partial_function_domain f S) x ->
  (forall S y, C x S -> partial_function_graph f S y -> y=c) ->
  covering_upper_limit C f x=c.
Proof.
move=> hf hval; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: le_trans (@covering_upper_limit_le_level R X C f x 1%R ltr01) _.
  apply: extended_real_sup_least=> y [S [hC [_ hy]]].
  by rewrite (hval S y hC hy).
- apply: extended_real_inf_greatest=> b [e [he ->]].
  have [S [[hC [y hy]] hd]] := (covering_relation_fine_iff_small_diameter _ _).1 hf e he.
  apply: extended_real_sup_upper; exists S; split=> //; split=> //.
  by rewrite -(hval S y hC hy).
Qed.
