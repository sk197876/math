(** Federer (1969), 2.4.10, p. 85: null changes of a density do not affect
    its upper integrals. This supporting fact follows from 2.4.3(2), p. 81,
    without assuming measurability. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP
  MeasureIntegralBounds MeasureIntegralAlmostEquality MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [measure_upper_integral_almost_equal]: supporting
    invariance of the upper integral under null changes of
    the density in Federer 2.4.10, p. 85; unlike
    signed-integral invariance, measurability is unnecessary. *)
Lemma measure_upper_integral_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  measure_almost_equal mu f g -> measure_upper_integral mu f = measure_upper_integral mu g.
Proof.
move=> he; have [hfg hgf] := @almost_equal_extended_order R X mu hm f g he.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@measure_upper_integral_monotone R X mu hm f g hfg).
- exact (@measure_upper_integral_monotone R X mu hm g f hgf).
Qed.
