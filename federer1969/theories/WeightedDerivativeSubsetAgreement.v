(** Supporting localisation in Federer (1969), 2.9.21, p. 166: curves and
    continuous factors may be replaced outside [a,b]. The two endpoints are
    Lebesgue-null; at interior points the actual derivatives agree by their
    two-sided quotient definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology CurveArcLength RealBVMonotoneDecomposition
  RealCurveDerivativeUP LocalRealDerivativeAgreement WeightedRealDerivativeIntegrand
  PartialFunctionUP PartialZeroExtension MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_derivative_subset_agreement]: supporting segment
    locality of the weighted derivative integral in Federer 2.9.21, p. 166
    Curves agreeing on the segment have the same actual derivative graph at
    every interior point. Almost-everywhere derivative existence for the
    original curve and nullity of both endpoints give almost equality of the
    zero-extended weighted integrands. *)
Lemma weighted_derivative_subset_agreement (R : realType) (f F g G : R -> R)
    (a b : R) : curve_locally_finite_variation (g : R -> real_line_metric R) ->
  (forall x, a<=x -> x<=b -> f x=F x) ->
  (forall x, a<=x -> x<=b -> g x=G x) ->
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_function_zero_extension (0 : extended_real_line R) `[a,b]
      (weighted_real_curve_derivative_integrand f g))
    (partial_function_zero_extension (0 : extended_real_line R) `[a,b]
      (weighted_real_curve_derivative_integrand F G)).
Proof.
move=> hg hF hG; have hm := lebesgue_scalar_is_measure R.
have hD := @real_bv_joint_derivatives_ae R g hg.
pose N := [set a] `|` [set b].
have hN : lebesgue_scalar_measure N=0%E.
  exact (@measure_null_union R (real_line_metric R) (@lebesgue_scalar_measure R) hm
    [set a] [set b] (lebesgue_scalar_singleton a) (lebesgue_scalar_singleton b)).
have hn : measure_almost_everywhere (@lebesgue_scalar_measure R) (~` N).
  by rewrite /measure_almost_everywhere setCK.
have hBoth := measure_almost_everywhere_and hm hD hn.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hBoth)=> x [[v [w [hv hrest]]] hxN].
case: (pselect ((`[a,b] : set (real_line_metric R)) x))=> hxA.
- have /andP[hax hxb] : a<=x<=b by move: hxA; rewrite /= in_itv.
  have hxa : x!=a by apply/eqP=> he; apply: hxN; left; exact he.
  have hxb' : x!=b by apply/eqP=> he; apply: hxN; right; exact he.
  have hax' : a<x by rewrite lt_neqAle eq_sym hxa hax.
  have hxb'' : x<b by rewrite lt_neqAle hxb' hxb.
  have hVG := (@real_derivative_segment_interior_agreement R g G a b x v hG hax' hxb'').1 hv.
  exists (f x*v)%:E; split.
  + apply/(partial_function_zero_extension_on _ _ _ hxA).
    apply/weighted_real_derivative_integrand_graph; by exists v; split.
  + apply/(partial_function_zero_extension_on _ _ _ hxA).
    apply/weighted_real_derivative_integrand_graph; exists v; split=> //.
    by rewrite (hF x hax hxb).
- exists 0; split; by apply/(partial_function_zero_extension_off _ _ _ hxA).
Qed.
