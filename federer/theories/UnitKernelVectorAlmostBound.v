(** Federer (1969), 4.1.14, p. 371: the positive normalized
    smoothing kernel preserves an almost-everywhere derivative norm
    bound on its actual nonzero locus. This is the original unit
    integral estimate of 4.1.2, pp. 346–347, with null sets retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureVectorIntegralUP
  SummableRealFunctionUP SummableRealArithmetic TotalVectorIntegralAlmostDominatedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_weight_vector_almost_bound]: the bound for
    the smoothed actual derivative in Federer 4.1.14, p. 371.
    Only a conull bound where the actual kernel is nonzero is
    needed. No symmetry, ambient finite measure, completeness or
    whole-target separability is assumed. *)
Theorem unit_weight_vector_almost_bound (R:realType) (X:choiceType)
    (Y:lmodType R) (N:Y->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu)
    (w:X->R) (F:X->Y) (y:Y) (C:R):
  (forall x,0<=w x) ->is_measure_integral mu (real_total_integrand w) (1:R)%:E ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(w x*:F x:real_norm_metric_space hN))) y ->
  measure_almost_everywhere mu [set x|w x!=0->N (F x)<=C] ->N y<=C.
Proof.
move=>hNonnegative hMass hIntegral hAE.
have hMajorant:=@real_total_integral_scale R X mu hm w 1 C hMass.
rewrite mulr1 in hMajorant.
apply:(@total_vector_integral_almost_dominated_norm R X Y N hN mu hm
  (fun x=>w x*:F x) y (fun x=>C*w x) C hIntegral hMajorant).
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAE)=>x hx.
change (is_true (N (w x*:F x)<=C*w x)).
rewrite (real_seminorm_scale hN.1) (ger0_norm (hNonnegative x)).
case:(eqVneq (w x) 0)=>[hZero|hNonzero].
- by rewrite hZero mul0r mulr0.
- rewrite mulrC;exact:(ler_wpM2r (hNonnegative x) (hx hNonzero)).
Qed.
