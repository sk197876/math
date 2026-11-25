(** Federer (1969), 4.1.2, p. 347: a
    uniform error on the nonzero part of a
    nonnegative unit-mass kernel bounds the difference
    of the actual weighted vector integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureVectorIntegralUP
  SummableRealFunctionUP SummableRealArithmetic TotalVectorIntegralArithmetic TotalVectorIntegralEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_weight_vector_difference_bound]: the
    uniform integral error used when differentiating
    the input factor of the convolution,
    Federer 4.1.2, p. 347. The
    domain of each actual integral is preserved. *)
Theorem unit_weight_vector_difference_bound (R:realType) (X:choiceType) (Y:lmodType R)
    (N:Y->R) (hN:is_real_norm N) (mu:set X->\bar R) (hm:is_measure mu)
    (w:X->R) (F G:X->Y) (y z:Y) (e:R):
  (forall x,0<=w x) ->is_measure_integral mu (real_total_integrand w) (1:R)%:E ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(w x*:F x:real_norm_metric_space hN))) y ->
  is_measure_vector_integral mu (partial_function_total (fun x=>(w x*:G x:real_norm_metric_space hN))) z ->
  (forall x,w x!=0 ->N (F x-G x)<=e) ->N (y-z)<=e.
Proof.
move=>hNonneg hMass hF hG hBound.
have hError:=@total_vector_integral_subtract R X Y N hN mu hm
  (fun x=>w x*:F x) (fun x=>w x*:G x) y z hF hG.
have hMajorant:=@real_total_integral_scale R X mu hm w 1 e hMass.
rewrite mulr1 in hMajorant.
apply:(@total_vector_integral_dominated_norm R X Y N hN mu hm
  (fun x=>w x*:F x-w x*:G x) (y-z) (fun x=>e*w x) e hError hMajorant)=>x.
rewrite -scalerBr (real_seminorm_scale hN.1) (ger0_norm (hNonneg x)).
have [hZero|hNonzero]:=eqVneq (w x) 0.
- by rewrite hZero mul0r mulr0.
- rewrite mulrC; exact:(ler_wpM2r (hNonneg x) (hBound x hNonzero)).
Qed.
