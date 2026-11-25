(** Federer (1969), 4.1.7, p. 359:
    integrate an actual compact scalar test's
    derivative up to b. Its earlier finite
    fundamental theorem and common compact support
    remove the unbounded endpoint; no improper
    integral theorem is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealNormUP RealMetricBackground NormDifferentialUP NormClassOneUP NormHigherCurveDerivativeUP
  RealClassOneSegmentIntegral LebesgueScalarMeasure MeasureIntegralUP MeasureSubsetIntegral
  RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_compact_primitive_left_integral]:
    integral_(-infinity,b] D=F(b) for
    an actual continuously differentiable compact
    test and its compact derivative, supporting
    the displayed primitive in Federer 4.1.7,
    p. 359. The value is an ordinary
    subset integral, not a default improper value. *)
Theorem real_compact_primitive_left_integral (R:realType) (F D:R->R) M:
  0<M ->
  (forall t,has_norm_differential (fun s:R^o=>`|s|) (fun s:R^o=>`|s|) (fun _=>True)
    F t (@scalar_coefficient_linear_map R R^o (D t))) ->
  norm_class_zero (fun s:R^o=>`|s|) (fun s:R^o=>`|s|) (fun _=>True) D ->
  (forall t,M<`|t| ->F t=0) ->(forall t,M<`|t| ->D t=0) ->
  forall b:R,is_measure_subset_integral (@lebesgue_scalar_measure R) [set t:R|t<=b]
    (real_total_integrand D) (F b)%:E.
Proof.
move=>hM hDifferential hD hFOff hDOff b.
pose a:=-(M+`|b|+1).
have hbBound: -b<=`|b| by have h:=ler_norm (-b);by rewrite normrN in h.
have hAbsB:0<=`|b| :=normr_ge0 _.
have hab:a<=b by rewrite /a;lra.
have haLower:a< -M by rewrite /a;lra.
have haAbs:M<`|a|.
  have h:=ler_norm (-a);rewrite normrN in h;lra.
have hAZero:F a=0:=hFOff a haAbs.
have hInterval:=@real_class_one_segment_integral R F D a b hab hDifferential hD.
rewrite hAZero subr0 in hInterval.
pose g t:=if pselect ((`[a,b]:set (real_line_metric R)) t) then D t else 0.
have hSegmentOn t:((`[a,b]:set (real_line_metric R)) t)->g t=D t.
  move=>ht;rewrite /g;case:pselect=>hSegment;first by [].
  exact:False_ind _ (hSegment ht).
have hSegmentOff t:(~((`[a,b]:set (real_line_metric R)) t))->g t=0.
  move=>ht;rewrite /g;case:pselect=>hSegment;last by [].
  exact:False_ind _ (ht hSegment).
have hIntegral:=(@real_subset_integral_total R (real_line_metric R) (@lebesgue_scalar_measure R)
  `[a,b] D g (F b)%:E hSegmentOn hSegmentOff).1 hInterval.
have hOn t:(t<=b)->g t=D t.
  move=>ht;rewrite /g;case:pselect=>hSegment;first by [].
  have hta:t<a.
    rewrite ltNge;apply/negP=>hat;apply:hSegment.
    by rewrite /= in_itv /= hat ht.
  have hAbs:M<`|t|.
    have h:=ler_norm (-t);rewrite normrN in h;lra.
  exact:esym (hDOff t hAbs).
have hOff t:(~(t<=b))->g t=0.
  move=>ht;rewrite /g;case:pselect=>hSegment;last by [].
  have /andP [_ htb]:is_true (a<=t<=b) by move:hSegment;rewrite /= in_itv /=.
  exact:False_ind _ (ht htb).
exact:((@real_subset_integral_total R (real_line_metric R) (@lebesgue_scalar_measure R)
  [set t:R|t<=b] D g (F b)%:E hOn hOff).2 hIntegral).
Qed.
