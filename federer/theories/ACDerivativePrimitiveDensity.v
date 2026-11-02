(** Federer (1969), 2.9.24, p. 169: apply 2.9.20(1), p. 165, to obtain the
    integral of g' on every partition cell. A total proof representative
    preserves these actual cell integrals by almost equality. The local
    Federer erratum has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology CurveArcLength
  StieltjesImageMeasures RealAbsoluteContinuityUP RealAbsoluteContinuity RealSegmentIntegralDifference
  RealDerivativeRepresentative RealCurveDerivativeIntegrands MeasureUP MeasureRestriction
  MeasureAlmostUP RestrictedAlmostEverywhere MeasureIntegralUP MeasureSubsetIntegral
  RestrictedIntegralIdentity LebesgueScalarMeasure TopologicalBorel BorelRegularMeasureUP
  IntervalBumpFunctions SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [absolutely_continuous_derivative_primitive_density]:
    supporting cell primitive identity in Federer 2.9.24,
    p. 169, by 2.9.20(1), p. 165. Every closed
    subinterval has the actual total-representative derivative
    integral g(v)-g(u), including singleton subintervals. *)
Theorem absolutely_continuous_derivative_primitive_density (R : realType) (g : R -> R)
    (a b : R) : curve_locally_finite_variation (g : R -> real_line_metric R) ->
  a<b -> is_absolutely_continuous_real_curve g a b ->
  forall u v : R, a<=u -> u<=v -> v<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v]
      (real_total_integrand (real_derivative_representative g)) (g v-g u)%:E.
Proof.
move=> hg hab hAC.
have [psip [psim hp]] := @induced_measure_pair_exists R g hg.
have hfull := @federer_2_9_20 R g psip psim a b hg hp hab.
have h2 := hfull.2.1.2 hAC.
have h1 := hfull.1.2 h2.
have hD := bv_real_derivative_representative_ae hg.
have hm := lebesgue_scalar_is_measure R.
move=> u v hau huv hvb.
have hi := @indefinite_derivative_integral_subsegment R g a b u v h1 hau huv hvb.
have hcell : measure_measurable (@lebesgue_scalar_measure R) (`[u,v] : set (real_line_metric R)).
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R)).
  apply: closed_borel_set; exact: segment_closed_real.
have hiR := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[u,v] (real_curve_derivative_integrand g)
  (g v-g u)%:E hcell).2 hi.
have hDR := @almost_everywhere_for_restricted_measure R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[u,v] _ hD.
have hrep := @real_derivative_representative_integral R
  (measure_restrict (@lebesgue_scalar_measure R) `[u,v])
  (measure_restrict_is_measure hm `[u,v]) g (g v-g u)%:E hDR hiR.
exact: (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm `[u,v]
  (real_total_integrand (real_derivative_representative g)) (g v-g u)%:E hcell).1 hrep.
Qed.
