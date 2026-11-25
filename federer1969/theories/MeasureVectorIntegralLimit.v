(** Federer (1969), 2.4.12, pp. 87–88: closedness of the subspace on which
    sigma(f) has a representing vector. The following sequential form
    identifies a target limit by every continuous real functional, using
    continuity of both scalar evaluation and its integral. It is the
    closedness step of the book's construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP
  MeasureUP MeasureLpMembershipUP MeasureLpConvergence ContinuousRealFunctional
  MeasureVectorIntegralUP MeasureFunctionalIntegral MeasureFunctionalIntegralConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_vector_integral_limit]: supporting sequential
    closedness in Federer 2.4.12, pp. 87–88 A limit of integral witnesses
    represents the L1 limit, with the full dual specification preserved. *)
Theorem measure_vector_integral_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN))
    (y : nat -> real_norm_metric_space hN) (z : real_norm_metric_space hN) :
  (forall n, is_measure_vector_integral mu (f n) (y n)) ->
  is_measure_lp_function mu 1%R g -> converges_in_lp_norm mu N 1%R f g ->
  y @ \oo --> z -> is_measure_vector_integral mu g z.
Proof.
move=> hi hg hl hy; split=> // a ha.
have [r hr] := @continuous_functional_evaluation_summable R X V N hN mu hm g a hg ha.
have hscalar := @functional_integral_converges R X V N hN mu hm f g a
  (fun n => (a (y n) : real_line_metric R)) r (fun n => (hi n).1) hg ha
  (fun n => (hi n).2 a ha) hr hl.
have htarget : (fun n => (a (y n) : real_line_metric R)) @ \oo --> (a z : real_line_metric R).
  move=> U hU; exact: hy _ (ha z U hU).
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter ((fun n => (a (y n) : real_line_metric R)) @ \oo) :=
  @fmap_proper_filter nat (real_line_metric R) (fun n => a (y n)) \oo PF0.
have he := @cvg_unique (real_line_metric R) (@metric_hausdorff R [the metricType R of real_line_metric R])
  _ PF r (a z) hscalar htarget.
by rewrite -he.
Qed.
