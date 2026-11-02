(** Federer (1969), 3.2.6, p. 246: almost
    every scalar level has a finite fibre consisting
    entirely of interior points with actual nonzero
    derivatives. The remainder image contains the endpoint
    levels and every undefined or zero-derivative preimage. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP LocallyAbsolutelyContinuousCurve
  ScalarCurveDerivativeLoci ScalarCurveRemainderNull ScalarCurveMultiplicityFinite
  MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_regular_fibres_almost]: the two
    almost-everywhere conditions and their regular-fibre
    consequence in Federer 3.2.6, p. 246. Both
    interval endpoints remain in the exceptional remainder. *)
Theorem scalar_regular_fibres_almost (R:realType) (f:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> a<b ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set y|
    (@mapping_multiplicity R [the choiceType of real_line_metric R] R f `[a,b] y< +oo)%E /\
    forall x,a<=x -> x<=b -> f x=y ->
      exists v:R,has_real_curve_derivative f x v /\ v!=0 /\ a<x /\ x<b].
Proof.
move=>hAC hab; have hm:=lebesgue_scalar_is_measure R.
have hFinite:=scalar_interval_multiplicity_finite hAC hab.
have hNull:=scalar_nonsigned_remainder_image_null hAC hab.
have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R)
    (~` (f @` scalar_nonsigned_derivative_remainder f a b)).
  by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_and hm hFinite hOff))=>y [hFy hy].
split; first exact hFy.
move=>x hax hxb hxy.
have hIx:(`[a,b]:set (real_line_metric R)) x by rewrite /= in_itv /= hax hxb.
have hSigns:(scalar_positive_derivative_set f a b `|` scalar_negative_derivative_set f a b) x.
  apply:contrapT=>hNot; apply:hy; exists x; last exact hxy.
  by split.
case:hSigns=>[[hRange [v [hv hp]]]|[hRange [v [hv hn]]]].
- move:hRange; rewrite /= in_itv /= =>/andP[hat htb].
  exists v; split; first exact hv; split; first by rewrite (gt_eqF hp).
  by split.
- move:hRange; rewrite /= in_itv /= =>/andP[hat htb].
  exists v; split; first exact hv; split; first by rewrite (lt_eqF hn).
  by split.
Qed.
