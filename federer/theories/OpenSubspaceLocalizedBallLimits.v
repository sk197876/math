(** Federer (1969), 4.1.5, p. 350:
    localized ambient ball quotients give the
    original open-subspace ball quotients at
    each interior point of the compact piece.
    The proof uses the exact image/restriction
    integrals and the original subspace metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import MetricSubsetBackground MetricClosedBalls MeasureUP MeasureRestriction MeasurePushforward
  SummableRealFunctionUP BallIntegralQuotientLimitUP BallIntegralQuotientLocality
  SubspaceLocalizedIntegral SubspaceSmallBallGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_subspace_localized_ball_limit]: the
    exact local-to-original ball-quotient transfer
    in Federer 4.1.5, p. 350, without
    a global finite-mass hypothesis on U. *)
Theorem open_subspace_localized_ball_limit (R:realType) (T:metricType R)
    (U C:set T) (mu:set (metric_subset U)->\bar R) (hm:is_measure mu)
    (f:metric_subset U->R) (g:T->R) (x:metric_subset U) (l:R):
  measure_measurable mu ((fun y:metric_subset U=>set_val y) @^-1` C) ->
  (forall y,g (set_val y)=f y) ->interior C (set_val x) ->
  is_ball_integral_quotient_limit
    (measure_pushforward (fun y:metric_subset U=>(set_val y:T))
      (measure_restrict mu ((fun y:metric_subset U=>set_val y) @^-1` C)))
    (real_total_integrand g) (set_val x) l ->
  is_ball_integral_quotient_limit mu (real_total_integrand f) x l.
Proof.
move=>hCMeasurable hValues hInterior hLimit.
have[cap [hCap hCapture]]:=@subspace_small_closed_ball_capture R T U C x hInterior.
apply:(@ball_integral_quotient_locality R (metric_subset U) T mu _
  (fun y:metric_subset U=>(set_val y:T)) (real_total_integrand f) (real_total_integrand g)
  x l cap hCap _ _ hLimit).
- move=>r hR hSmall.
  have hSubset:(fun y:metric_subset U=>set_val y) @^-1` metric_closed_ball (set_val x) r `<=`
      (fun y:metric_subset U=>set_val y) @^-1` C.
    by move=>y hy; exact:(hCapture r hR hSmall (set_val y) hy).
  have hMass:=@subspace_localized_mass R T U mu ((fun y:metric_subset U=>set_val y) @^-1` C)
    (metric_closed_ball (set_val x) r) hSubset.
  by rewrite subspace_closed_ball_preimage in hMass.
- move=>r hR hSmall J hJ.
  have hSubset:(fun y:metric_subset U=>set_val y) @^-1` metric_closed_ball (set_val x) r `<=`
      (fun y:metric_subset U=>set_val y) @^-1` C.
    by move=>y hy; exact:(hCapture r hR hSmall (set_val y) hy).
  have hOriginal:=@subspace_localized_subset_integral R T U mu hm
    ((fun y:metric_subset U=>set_val y) @^-1` C) f g (metric_closed_ball (set_val x) r)
    J%:E hCMeasurable hValues hSubset hJ.
  by rewrite subspace_closed_ball_preimage in hOriginal.
Qed.
