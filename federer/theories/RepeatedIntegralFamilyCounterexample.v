(** Federer (1969), 2.6.3(3), p. 118: the family of sets having the
    specified repeated characteristic integral need not be a Borel family.
    We retain Federer's hypotheses and orientation. The local erratum has no
    correction to this example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureSplit
  MeasureIntegralUP ProductSections BorelFamilyUP BorelFamilyBasic RepeatedIntegralSetUP
  RepeatedIntegralMeasurableSections PositiveCharacteristicMeasurability SwitchedRectangleSections RepeatedRectangleIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [switched_rectangle_repeated_integrable]: the
    assertion S belongs to F in Federer 2.6.3(3),
    p. 118. Its inner-integral function is the common
    nonnegative constant alpha(A1)=alpha(A2), even if this value
    is infinite. No measurability assumption on B is needed. *)
Lemma switched_rectangle_repeated_integrable (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A1 A2 : set X) (B : set Y) :
  measure_measurable alpha A1 -> measure_measurable alpha A2 -> alpha A1=alpha A2 ->
  is_repeatedly_integrable_set alpha beta (switched_rectangle_set A1 A2 B).
Proof.
move=> h1 h2 he.
have hm y : measure_measurable alpha (product_horizontal_section (switched_rectangle_set A1 A2 B) y).
  case: (pselect (B y))=> hy.
  - by rewrite (switched_horizontal_section_on A1 A2 hy).
  - by rewrite (switched_horizontal_section_off A1 A2 hy).
apply: (@repeated_integral_measurable_sections_iff R X Y alpha beta ha _ hm).2.
have hv : (fun y => alpha (product_horizontal_section (switched_rectangle_set A1 A2 B) y)) = (fun _ => alpha A1).
  apply: funext=> y; case: (pselect (B y))=> hy.
  - by rewrite (switched_horizontal_section_on A1 A2 hy).
  - by rewrite (switched_horizontal_section_off A1 A2 hy) he.
rewrite hv; exists (alpha A1*beta setT).
exact (@nonnegative_extended_constant_integral R Y beta hb (alpha A1) (measure_nonnegative ha A1)).
Qed.

(** Source for [repeated_integral_family_not_borel]: complete
    counterexample Federer 2.6.3(3), p. 118. For
    disjoint measurable A1,A2 of equal positive measure and
    a nonmeasurable B, the stated S and T belong to F,
    but their intersection does not. Consequently F is not
    a Borel family in the sense of 2.2.1, pp. 59–60. *)
Theorem repeated_integral_family_not_borel (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A1 A2 : set X) (B : set Y) :
  (forall x, A1 x -> A2 x -> False) ->
  measure_measurable alpha A1 -> measure_measurable alpha A2 ->
  alpha A1=alpha A2 -> 0 < alpha A1 -> ~ measure_measurable beta B ->
  let S := switched_rectangle_set A1 A2 B in
  let T := A1 `*` @setT Y in
  is_repeatedly_integrable_set alpha beta S /\
  is_repeatedly_integrable_set alpha beta T /\
  ~ is_repeatedly_integrable_set alpha beta (S `&` T) /\
  ~ is_borel_family (@setT (X * Y)) (is_repeatedly_integrable_set alpha beta).
Proof.
move=> hd h1 h2 he hp hB S T.
have hS := @switched_rectangle_repeated_integrable R X Y alpha beta ha hb A1 A2 B h1 h2 he.
have hT := @repeated_rectangle_integrable R X Y alpha beta ha hb A1 setT h1 (measure_measurable_whole hb).
have hnot : ~ is_repeatedly_integrable_set alpha beta (S `&` T).
  rewrite /S /T (switched_rectangle_intersection B hd)=> h.
  exact: hB (@repeated_positive_rectangle_requires_measurability R X Y alpha beta ha A1 B h1 hp h).
split=> //; split=> //; split=> // hF.
apply: hnot; exact (@borel_family_binary_intersection (X * Y)%type setT _ hF S T hS hT).
Qed.
