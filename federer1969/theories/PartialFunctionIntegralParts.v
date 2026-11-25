(** Federer (1969), 2.4.4(6)–(8), p. 82, proof p. 83: positive and negative
    parts and their pointwise difference. The extended scalar laws were
    established in 2.1.1; this file lifts them to exact partial graphs.
    Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialFunctionGraphEquivalence PartialExtendedArithmetic MeasureIntegralNegation MeasureUpperIntegralPositivePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [partial_extended_function_negative_part]: the
    negative part f- in Federer 2.4.4(6), p. 82,
    with the same partial domain as f. *)
Definition partial_extended_function_negative_part (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  partial_function_postcompose f (fun y => (extended_negative_part y : extended_real_line R)).

(** Source for [partial_negative_part_negation_graph]: supporting
    identity f-=(-f)+ in Federer 2.4.4(6), proof p. 83. *)
Lemma partial_negative_part_negation_graph (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_positive_part (partial_extended_function_negate f)) x y <->
  partial_function_graph (partial_extended_function_negative_part f) x y.
Proof. exact: partial_function_postcomposition_associative. Qed.

(** Source for [partial_parts_difference_graph]: exact partial-
    domain form of f=f+-f- used in Federer 2.4.4(6),
    proof p. 83. At least one part vanishes at each
    defined point, so the difference is always defined there. *)
Lemma partial_parts_difference_graph (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_add (partial_extended_function_positive_part f)
    (partial_extended_function_negate (partial_extended_function_negative_part f))) x y <->
  partial_function_graph f x y.
Proof.
split.
- move=> h; have [p [n [[a [ha hap]] [[m [[b [hb hbm]] hmn]] hpn]]]] :=
    (@partial_extended_function_add_graph R X _ _ x y).1 h.
  have hab := partial_function_single_valued ha hb.
  rewrite -hab in hbm; rewrite -hap -hmn -hbm in hpn.
  change (extended_subtract (extended_positive_part a) (extended_negative_part a)=Some y) in hpn.
  rewrite extended_positive_negative_parts in hpn; case: hpn=> he; by rewrite -he.
- move=> hy; apply/partial_extended_function_add_graph.
  exists (extended_positive_part y),(-extended_negative_part y); split.
  + exists y; by split.
  split.
  + exists (extended_negative_part y); split=> //; exists y; by split.
  + exact: extended_positive_negative_parts.
Qed.
