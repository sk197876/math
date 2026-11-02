(** Federer (1969), 3.1.11, p. 220:
    the one-variable Taylor integral remainder, first
    in its equivalent ordinary-integral form. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP
  NormHigherCurveDerivativeUP NormedStieltjesUP NormedStieltjesLaws
  WeightedCurvePrimitive WeightedCurveIntegral ScalarTaylorWeights
  ScalarTaylorWeightIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_curve_taylor_integral]:
    repeated integration by parts for a finite
    derivative chain, Federer 3.1.11, p. 220.
    Only continuity of the highest derivative and
    existence of the preceding derivatives are used. *)
Theorem norm_curve_taylor_integral (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (F : nat->R->Y) k :
  (forall t, 0<=t<= 1 -> A t) ->
  (forall i, (i<=k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A (F i) a
      (scalar_coefficient_linear_map (F i.+1 a))) ->
  norm_class_zero (fun t : R^o=>`|t|) NY A (F k.+1) ->
  has_normed_stieltjes_integral NY
    (fun t=>scalar_taylor_weight k t*:F k.+1 t) (fun t=>t) 0 1
    (F 0%N 1-\sum_(i < k.+1) (((i`!)%:R)^-1*:F i 0)).
Proof.
move=> hA hF hc.
have hO a ha := (hc a ha).1.
have hW0 t (_ : A t) := scalar_taylor_weight_zero t.
have hW i (_ : (i<k)%N) a ha := @scalar_taylor_weight_differential R A a i (hO a ha).
have hi := weighted_curve_integral hNY hA hW0
  (@scalar_taylor_weight_upper R) hF hW
  (@scalar_taylor_weight_continuous R A k hO) hc.
have hsum : weighted_curve_primitive (@scalar_taylor_weight R) F k 0=
    \sum_(i < k.+1) (((i`!)%:R)^-1*:F i 0).
  apply: eq_bigr=>i _; by rewrite scalar_taylor_weight_lower.
by rewrite hsum in hi.
Qed.

(** Source for [norm_curve_taylor_riemann_remainder]:
    the Taylor remainder after subtracting the
    highest derivative at zero, Federer 3.1.11,
    p. 220. The integrand is the difference
    of the highest derivatives with the factorial
    polynomial weight; its integral exists in Y. *)
Theorem norm_curve_taylor_riemann_remainder (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (F : nat->R->Y) k :
  (forall t, 0<=t<= 1 -> A t) ->
  (forall i, (i<=k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A (F i) a
      (scalar_coefficient_linear_map (F i.+1 a))) ->
  norm_class_zero (fun t : R^o=>`|t|) NY A (F k.+1) ->
  has_normed_stieltjes_integral NY
    (fun t=>scalar_taylor_weight k t*:(F k.+1 t-F k.+1 0)) (fun t=>t) 0 1
    (F 0%N 1-\sum_(i < k.+2) (((i`!)%:R)^-1*:F i 0)).
Proof.
move=> hA hF hc.
have hi := norm_curve_taylor_integral hNY hA hF hc.
have hj := scalar_taylor_weight_integral_constant hNY (F k.+1 0) k.
have hs := normed_stieltjes_integral_subtract hNY hi hj.
have hsum : F 0%N 1-\sum_(i < k.+2) (((i`!)%:R)^-1*:F i 0)=
    (F 0%N 1-\sum_(i < k.+1) (((i`!)%:R)^-1*:F i 0))-
      (((k.+1)`!)%:R)^-1*:F k.+1 0.
  by rewrite big_ord_recr opprD addrA.
rewrite -hsum in hs.
apply: normed_stieltjes_integral_ext _ _ hs=>t //.
by rewrite scalerBr.
Qed.
