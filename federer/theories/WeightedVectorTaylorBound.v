(** Federer (1969), 4.1.2, p. 347: the
    compact scalar Taylor bound controls the actual
    vector-integral remainder. The earlier vector integral
    addition, scalar multiplication and norm laws are reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasureIntegralUP
  MeasureVectorIntegralUP SummableRealFunctionUP SummableRealArithmetic
  TotalVectorIntegralArithmetic TotalVectorIntegralEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_vector_integral_taylor_bound]: the
    derivative computation under the integral in Federer
    4.1.2, p. 347, with the Taylor
    error bounded on one fixed compact source set. *)
Theorem weighted_vector_integral_taylor_bound (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (K:X->Prop) (f:X->Y) (w v q:X->R) (yw yv yq:Y) (b t c:R):
  is_measure_integral mu
    (real_total_integrand (fun x=>if pselect (K x) then N (f x) else 0)) b%:E ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(w x*:f x:real_norm_metric_space hN))) yw ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(v x*:f x:real_norm_metric_space hN))) yv ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(q x*:f x:real_norm_metric_space hN))) yq ->
  (forall x,K x ->`|w x-v x-t*q x|<=c) ->
  (forall x,~K x ->w x=0 /\ v x=0 /\ q x=0) ->N (yw-yv-t*:yq)<=c*b.
Proof.
move=>hNorm hw hv hq hBound hOff.
have hDiff:=@total_vector_integral_subtract R X Y N hN mu hm
  (fun x=>w x*:f x) (fun x=>v x*:f x) yw yv hw hv.
have hScale:=@total_vector_integral_scale R X Y N hN mu hm (fun x=>q x*:f x) yq t hq.
have hError:=@total_vector_integral_subtract R X Y N hN mu hm
  (fun x=>w x*:f x-v x*:f x) (fun x=>t*:(q x*:f x))
  (yw-yv) (t*:yq) hDiff hScale.
have hMajorant:=@real_total_integral_scale R X mu hm
  (fun x=>if pselect (K x) then N (f x) else 0) b c hNorm.
apply:(@total_vector_integral_dominated_norm R X Y N hN mu hm
  (fun x=>w x*:f x-v x*:f x-t*:(q x*:f x)) (yw-yv-t*:yq)
  (fun x=>c*(if pselect (K x) then N (f x) else 0)) (c*b) hError hMajorant)=>x.
rewrite scalerA -!scalerBl (real_seminorm_scale hN.1).
case:(pselect (K x))=>hx.
- exact:(ler_wpM2r (real_seminorm_nonnegative hN.1 (f x)) (hBound x hx)).
- have [-> [-> ->]]:=hOff x hx.
  by rewrite mulr0 !subrr normr0 mul0r mulr0.
Qed.
