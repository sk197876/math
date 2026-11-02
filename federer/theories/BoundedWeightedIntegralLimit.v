(** Federer (1969), 2.9.24, p. 169: apply bounded convergence to bounded
    approximations multiplied by a summable derivative density. This
    supporting abstract lemma isolates that application of 2.4.9, p. 85. The
    approximations need converge only where the density is nonzero. The
    local Federer erratum has no entry for this application. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP
  PartialAbsolutePartsGraph PartialExtendedOrderLoci PartialDominatedConvergence
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasureBoundedConvergence ExtendedRealOrderLimit
  ExtendedIncreasingLimitSupremum RealErrorOrderLimit RealFiniteSequenceScaleLimit
  SummableRealFunctionUP SummableRealArithmetic TotalScalarLpUP TotalLoneSummability TotalScalarPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_weighted_integral_limit]: supporting complete
    bounded-convergence step for Federer 2.9.24, p. 169.
    The supplied integral values converge to B; the actual
    integral of F times the density q therefore equals B.
    Bounds can be zero, q may have either sign, and the
    ambient measure need not be finite or sigma finite. *)
Theorem bounded_weighted_integral_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> R) (F q : X -> R) (M : R) (a : nat -> R) (B : R) :
  summable_real_functions mu q ->
  is_measure_measurable_function mu (total_scalar_function F) ->
  0<=M -> (forall x, `|F x|<=M) -> (forall n x, `|f n x|<=M) ->
  measure_almost_everywhere mu [set x | q x=0 \/
    extended_order_limit (fun n => (f n x)%:E) (F x)%:E] ->
  (forall n, is_measure_integral mu (real_total_integrand (fun x => f n x*q x)) (a n)%:E) ->
  extended_order_limit (fun n => (a n)%:E) B%:E ->
  is_measure_integral mu (real_total_integrand (fun x => F x*q x)) B%:E.
Proof.
move=> hq hF hM hFb hfb hlim hi ha.
have hq1 := @summable_real_total_lone R X mu hm q hq.
have hFB : measure_almost_everywhere mu [set x | `|F x|<=M].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exact: hFb x.
have [c [hFc _]] := @total_scalar_pairing_bounded_factor R X mu hm q F M hq1 hF hM hFB.
have hcomm : (fun x => q x*F x)=(fun x => F x*q x).
  apply: funext=> x; exact: mulrC.
rewrite hcomm in hFc.
have [d hd] := @summable_real_absolute R X mu hm q hq.
have hH := @real_total_integral_scale R X mu hm _ d M hd.
have hdom n : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand (fun x => f n x*q x)))
    (real_total_integrand (fun x => M*`|q x|))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (`|f n x*q x|)%:E,(M*`|q x|)%:E; split.
  - exists (f n x*q x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first by apply/real_total_integrand_graph.
    rewrite lee_fin normrM; exact (ler_wpM2r (normr_ge0 (q x)) (hfb n x)).
have hconv : measure_almost_everywhere mu (partial_extended_convergence_locus
    (fun n => real_total_integrand (fun x => f n x*q x))
    (real_total_integrand (fun x => F x*q x))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlim)=> x hx.
  exists (fun n => (f n x*q x)%:E),(F x*q x)%:E; split.
  - by move=> n; apply/real_total_integrand_graph.
  - split; first by apply/real_total_integrand_graph.
    case: hx=> [hq0|hL].
    * apply: real_error_extended_order_limit=> e he; exists 0%N=> n _.
      by rewrite hq0 !mulr0 subrr normr0.
    * exact: real_finite_sequence_limit_right_scale.
have [cN [eN [C [hcN [hC [_ [_ hCcv]]]]]]] := @measure_bounded_convergence R X mu hm
  (fun n => real_total_integrand (fun x => f n x*q x))
  (real_total_integrand (fun x => F x*q x))
  (real_total_integrand (fun x => M*`|q x|))
  (ex_intro _ (M*d) hH) (fun n => (hi n).1) hFc.1 hdom hconv.
have hValues : cN=a.
  apply: funext=> n; exact: EFin_inj (measure_integral_unique (hcN n) (hi n)).
rewrite hValues in hCcv.
have heq := extended_order_limit_unique hCcv ha.
by rewrite -heq.
Qed.
