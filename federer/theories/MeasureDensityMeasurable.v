(** Federer (1969), 2.4.10, p. 85: every phi-measurable set is
    psi-measurable for the upper-integral density measure. We prove its
    Caratheodory splitting directly using restricted upper step functions;
    no measurability of the density is needed. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureSplit MeasureAlmostUP PartialExtendedOrderLoci MeasureIntegralBounds MeasureSubsetIntegral
  MeasureDensityUP MeasureDensityCover MeasureUpperIntegralSplitting ZeroExtensionNonnegative MeasureBoundGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_preserves_measurable_sets]: direct
    preservation of measurable sets in Federer 2.4.10,
    p. 85, for an almost-everywhere nonnegative density
    that need not be measurable. *)
Theorem measure_density_preserves_measurable_sets (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (A : set X) :
  is_measure_density mu h nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  measure_measurable mu A -> measure_measurable nu A.
Proof.
move=> hn hp hA T; have hnu := @measure_density_is_measure R X mu nu hm h hn hp.
apply/eqP; rewrite eq_le (measure_split_upper hnu) /=.
pose f := partial_function_zero_extension (0 : extended_real_line R) T h.
have hfp := @zero_extension_nonnegative_almost R X mu hm T h hp.
have hsplit := @measure_nonnegative_upper_split_lower_bound R X mu hm A f hA hfp.
have he1 : measure_upper_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f) = nu (T `&` A).
  rewrite (hn (T `&` A)); apply: measure_upper_integral_graph_equivalent=> x y.
  by rewrite /f partial_zero_extension_intersection_graph (setIC A T).
have he2 : measure_upper_integral mu (partial_function_zero_extension (0 : extended_real_line R) (~` A) f) = nu (T `\` A).
  rewrite (hn (T `\` A)); apply: measure_upper_integral_graph_equivalent=> x y.
  by rewrite /f partial_zero_extension_intersection_graph (setIC (~` A) T) setDE.
rewrite he1 he2 in hsplit.
have heT : measure_upper_integral mu f = nu T := esym (hn T).
by rewrite heT in hsplit.
Qed.
