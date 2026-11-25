(** Federer (1969), 2.9.22, p. 167: extend the implication (4)=>(1) of
    2.9.20, p. 166, to the actual Banach-valued derivative integral. The
    derivative's full L1 membership is proved independently. Every
    continuous dual evaluation then has the scalar endpoint integral from
    the printed corollary, proving the vector identity by its abstract
    defining laws. No relevant erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground CompleteMetricUP ContinuousRealFunctional
  ContinuousDualUP CurveArcLength NormedCurveDerivativeUP NormedCurveAbsoluteContinuityUP
  NormedBVInducedDerivates BVDerivativeLocalIntegrability NormedDerivativeScalarIntegralAgreement
  RealAbsoluteContinuityUP ContinuousInducedIntegralRepresentation StieltjesImageMeasures
  MeasureVectorIntegralUP MeasureUP MeasureAlmostUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureRestriction LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_continuous_induced_integral_representation]:
    direct (4)=>(1) part of Federer 2.9.22, p. 167, extending
    2.9.20, p. 166. Relative norm continuity gives relative
    continuity of each scalar evaluation; its actual induced pair
    supplies the scalar primitive identity. The proved partial-domain
    agreement transfers it to evaluation of the vector derivative.
    Full L1 membership and all such scalar identities are exactly the
    actual vector integral laws. No global endpoint continuity or
    prior total derivative representative is introduced. *)
Theorem normed_continuous_induced_integral_representation (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> real_norm_metric_space hN) (a b : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] -> a<b ->
  normed_curve_continuous_induced_measures hN ed g a b ->
  normed_curve_indefinite_derivative_integral hN g a b.
Proof.
move=> hY hg he hab [hc hPairs] x hax hxb.
split; first exact (@normed_bv_derivative_interval_lone R E N hN g hY hg he a x hax).
move=> f hf.
have hfc : is_continuous_real_functional hN (hom_as_linear (hom_of_linear f)) := hf.
have [alpha hAlpha] := @continuous_dual_surjective R E N hN D ed DN hD (hom_of_linear f) hfc.
have hScalarBV := @normed_bv_scalarisation R E D N hN ed DN hD g hg alpha.
have [psip [psim hp]] := @induced_measure_pair_exists R (fun t => ed alpha (g t)) hScalarBV.
have hScalarC : {within (`[a,b] : set (real_line_metric R)),
    continuous ((fun t => ed alpha (g t)) : real_line_metric R -> real_line_metric R)}.
  move=> z.
  have hAlphaC := continuous_dual_continuous hD (a:=alpha).
  exact: continuous_comp (hc z) (hAlphaC (g z)).
have hCond : real_curve_continuous_induced_measures (fun t => ed alpha (g t)) psip psim a b.
  split=> //; exact: hPairs alpha psip psim hp.
have hPrimitive := @continuous_induced_integral_representation R (fun t => ed alpha (g t))
  psip psim a b hScalarBV hp hab hCond.
have hA : measure_measurable (@lebesgue_scalar_measure R) (`[a,x] : set (real_line_metric R)).
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R a x).
have hInt := @normed_derivative_evaluation_restricted_integral R E D N hN ed DN hD g
  `[a,x] alpha (ed alpha (g x)-ed alpha (g a)) he hA (hPrimitive x hax hxb).
have hVal : ed alpha (g x)-ed alpha (g a)=f (g x-g a).
  by rewrite hAlpha !hom_of_linearE linearB.
rewrite hVal in hInt.
apply: (@measure_integral_graph_equivalent R (real_line_metric R)
  (measure_restrict (@lebesgue_scalar_measure R) (`[a,x] : set (real_line_metric R)))
  _ _ (f (g x-g a))%:E _ hInt)=> t y; split.
- move=> [v [hv hvy]]; exists v; split=> //.
  by rewrite hom_as_linearE hAlpha hom_of_linearE in hvy.
- move=> [v [hv hvy]]; exists v; split=> //.
  by rewrite hom_as_linearE hAlpha hom_of_linearE.
Qed.
