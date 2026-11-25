(** Federer (1969), 2.9.11, p. 158: choose a phi hull of A before comparing
    its density with a characteristic function. Here the original class M
    permits a Borel hull, obtained from finite local hulls on the bounded
    Borel partition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureHull
  MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP MeasurableAlmostModification
  MeasureDerivationContext MeasureRestriction MeasureDerivates DerivationBorelHulls
  RestrictionHullDerivates CharacteristicFunctionUP CharacteristicFunctionSealed
  CharacteristicDifferentiation MeasureCharacteristicIntegral SummableRealFunctionUP MeasureDensityPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_agreement_graph_levels]: supporting pointwise
    inference from the characteristic limit in Federer 2.9.11, p. 158 At a
    point of agreement, the one-level is precisely membership in B and the
    zero-level precisely nonmembership. *)
Lemma characteristic_agreement_graph_levels (R : realType) (X : Type)
    (B : set X) (s : X -> R) (f : partial_function X (extended_real_line R)) x :
  is_characteristic_function B s -> partial_function_graph f x (s x)%:E ->
  (partial_function_graph f x 1 <-> B x) /\
  (partial_function_graph f x 0 <-> ~ B x).
Proof.
move=> hs hd; case: (pselect (B x))=> hx.
- rewrite (characteristic_on_set hs hx) in hd; split.
  + split=> // _; exact hd.
  + split.
    * move=> hzero; exfalso.
      by move: (partial_function_single_valued hd hzero)=> /eqP; rewrite eqe oner_eq0.
    * by move=> hn; exfalso; exact: hn hx.
- rewrite (characteristic_off_set hs hx) in hd; split.
  + split.
    * move=> hone; exfalso.
      by move: (partial_function_single_valued hone hd)=> /eqP; rewrite eqe oner_eq0.
    * by move=> hb; exfalso; exact: hx hb.
  + split=> // _; exact hd.
Qed.

(** Source for [hull_restriction_derivate_characteristic]: supporting
    derivate/characteristic agreement for a measurable hull in Federer
    2.9.11, p. 158 The original arbitrary restriction has the same cell
    ratios as the hull restriction. No regularity of the former is asserted. *)
Lemma hull_restriction_derivate_characteristic (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) (s : X -> R) :
  is_measure_derivation_context phi V -> is_measure_hull phi A B ->
  is_characteristic_function B s ->
  measure_almost_equal phi (measure_derivate (measure_restrict phi A) phi V) (real_total_integrand s).
Proof.
move=> hc hB hs; have hm := derivation_measure_law (derivation_context_measure hc).
have ha := @characteristic_derivate_agreement R X phi V B s hc (measure_hull_measurable hB) hs.
have hg := @restriction_hull_derivate_graph R X phi V A B hc hB.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ ha)=> x [y [hy hsy]].
exists y; split=> //; exact: (hg x y).2 hy.
Qed.

(** Source for [density_one_points_hull_agreement]: direct null
    symmetric-difference inference for P and B in Federer 2.9.11, p. 158
    Agreement is stated as an almost-everywhere logical equivalence on
    actual graph levels. *)
Lemma density_one_points_hull_agreement (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A B : set X) :
  is_measure_derivation_context phi V -> is_measure_hull phi A B ->
  measure_almost_everywhere phi [set x | measure_density_one_points phi V A x <-> B x].
Proof.
move=> hc hB; have hm := derivation_measure_law (derivation_context_measure hc).
pose s := @CharacteristicFunction.value R X B.
have hs := @CharacteristicFunction.laws R X B.
have ha := @hull_restriction_derivate_characteristic R X phi V A B s hc hB hs.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ ha)=> x [y [hy hsy]].
have he := (real_total_integrand_graph s x y).1 hsy.
rewrite -he in hy; exact: (@characteristic_agreement_graph_levels R X B s _ x hs hy).1.
Qed.

(** Source for [density_complement_zero_points_hull_agreement]: direct null
    symmetric-difference inference for Q and X minus C in Federer 2.9.11, p.
    158 Here C is a hull of the complement of the original set A. *)
Lemma density_complement_zero_points_hull_agreement (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A C : set X) :
  is_measure_derivation_context phi V -> is_measure_hull phi (~` A) C ->
  measure_almost_everywhere phi [set x | measure_density_complement_zero_points phi V A x <-> ~ C x].
Proof.
move=> hc hC; have hm := derivation_measure_law (derivation_context_measure hc).
pose s := @CharacteristicFunction.value R X C.
have hs := @CharacteristicFunction.laws R X C.
have ha := @hull_restriction_derivate_characteristic R X phi V (~` A) C s hc hC hs.
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ ha)=> x [y [hy hsy]].
have he := (real_total_integrand_graph s x y).1 hsy.
rewrite -he in hy; exact: (@characteristic_agreement_graph_levels R X C s _ x hs hy).2.
Qed.

(** Source for [measurable_set_restriction_derivate]: supporting
    measurability of the raw set-density function in Federer
    2.9.11, p. 158. Choose the Borel hull supplied by M,
    differentiate its characteristic, and transfer measurability by
    almost equality. The arbitrary set A need not be measurable. *)
Theorem measurable_set_restriction_derivate (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context phi V ->
  @is_measure_measurable_function R X (extended_real_line R) phi
    (measure_derivate (measure_restrict phi A) phi V).
Proof.
move=> hc; have hm := derivation_measure_law (derivation_context_measure hc).
have [B [_ hB]] := @derivation_measure_borel_hull R X phi A (derivation_context_measure hc).
pose s := @CharacteristicFunction.value R X B.
have hs := @CharacteristicFunction.laws R X B.
have hchar := (@measure_characteristic_integral R X phi hm B s hs (measure_hull_measurable hB)).1.
have ha := @hull_restriction_derivate_characteristic R X phi V A B s hc hB hs.
apply: (@measurable_function_almost_equal R X (extended_real_line R) phi hm _ _ hchar).
exact: measure_almost_equal_sym ha.
Qed.
