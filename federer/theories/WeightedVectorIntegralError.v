(** Federer (1969), 4.1.2, p. 347: a
    compact scalar bound on the difference of two
    kernel weights controls the difference of their
    actual vector integrals. This estimate uses local
    norm integrability on that compact set only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasureIntegralUP
  MeasureVectorIntegralUP SummableRealFunctionUP SummableRealArithmetic
  TotalVectorIntegralArithmetic TotalVectorIntegralEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_vector_integral_difference_bound]: the
    original compact kernel error estimate used in
    Federer 4.1.2, p. 347. The integral
    witnesses need no global integrability of f. *)
Theorem weighted_vector_integral_difference_bound (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (K:X->Prop) (f:X->Y) (w v:X->R) (y z:Y) (b c:R):
  is_measure_integral mu
    (real_total_integrand (fun x=>if pselect (K x) then N (f x) else 0)) b%:E ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(w x*:f x:real_norm_metric_space hN))) y ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(v x*:f x:real_norm_metric_space hN))) z ->
  (forall x,K x ->`|w x-v x|<=c) ->
  (forall x,~K x ->w x=0 /\ v x=0) ->N (y-z)<=c*b.
Proof.
move=>hNorm hw hv hBound hOff.
have hDiff:=@total_vector_integral_subtract R X Y N hN mu hm
  (fun x=>w x*:f x) (fun x=>v x*:f x) y z hw hv.
have hMajorant:=@real_total_integral_scale R X mu hm
  (fun x=>if pselect (K x) then N (f x) else 0) b c hNorm.
apply:(@total_vector_integral_dominated_norm R X Y N hN mu hm
  (fun x=>w x*:f x-v x*:f x) (y-z)
  (fun x=>c*(if pselect (K x) then N (f x) else 0)) (c*b) hDiff hMajorant)=>x.
rewrite -scalerBl (real_seminorm_scale hN.1).
case:(pselect (K x))=>hx.
- exact:(ler_wpM2r (real_seminorm_nonnegative hN.1 (f x)) (hBound x hx)).
- have [-> ->]:=hOff x hx.
  by rewrite subrr normr0 mul0r mulr0.
Qed.
