(** Federer (1969), 3.1.11, p. 220:
    the printed one-variable Taylor formula, with
    the Stieltjes integrator (1-t)^k and
    the difference of highest derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialArithmetic NormClassOneUP NormClassZeroArithmetic
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra
  ScalarTaylorWeights NormedStieltjesUP NormedStieltjesLaws
  NormCurveTaylorIntegral NormedStieltjesDifferentiableIntegrator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [taylor_power_integrator_differential]:
    the derivative of the Stieltjes integrator
    (1-t)^(k+1), supporting the final displayed
    scalar-source Taylor formula in Federer 3.1.11,
    p. 220. *)
Lemma taylor_power_integrator_differential (R : realType)
    (A : R->Prop) a k :
  norm_domain_interior (fun t : R^o=>`|t|) A a ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun t=>(1-t)^+k.+1) a
    (@scalar_coefficient_linear_map R R^o
      (-((k.+1)`!)%:R*scalar_taylor_weight k a)).
Proof.
move=> hA.
pose c : R := ((k.+1)`!)%:R.
have hc : c!= 0 by rewrite /c pnatr_eq0 -lt0n fact_gt0.
have hs := norm_differential_scale (@scalar_absolute_value_norm R)
  (@scalar_absolute_value_norm R) c (@scalar_taylor_weight_differential R A a k hA).
rewrite -scalar_coefficient_linear_scale in hs.
change (has_norm_differential (fun t : R^o=>`|t|)
  (fun t : R^o=>`|t|) A (fun t=>c*scalar_taylor_weight k.+1 t) a
  (@scalar_coefficient_linear_map R R^o (c*(-scalar_taylor_weight k a)))) in hs.
rewrite mulrN -mulNr in hs.
apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R) _ hs).
move=> t ht; by rewrite /scalar_taylor_weight -/c mulrCA mulfV // mulr1.
Qed.

(** Source for [norm_curve_taylor_stieltjes]:
    Federer 3.1.11, p. 220, the last
    scalar-source displayed identity. In words:
    f(1) minus its Taylor polynomial of order
    k+1 at zero is the integral of
    [f^(k+1)(0)-f^(k+1)(t)]/(k+1)!
    against d(1-t)^(k+1). The finite
    derivative-chain hypotheses follow from class k+1. *)
Theorem norm_curve_taylor_stieltjes (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (F : nat->R->Y) k :
  (forall t, 0<=t<= 1 -> A t) ->
  (forall i, (i<=k)%N -> forall a, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A (F i) a
      (scalar_coefficient_linear_map (F i.+1 a))) ->
  norm_class_zero (fun t : R^o=>`|t|) NY A (F k.+1) ->
  has_normed_stieltjes_integral NY
    (fun t=>(((k.+1)`!)%:R)^-1*:(F k.+1 0-F k.+1 t))
    (fun t=>(1-t)^+k.+1) 0 1
    (F 0%N 1-\sum_(i < k.+2) (((i`!)%:R)^-1*:F i 0)).
Proof.
move=> hA hF hc.
have hO a ha := (hc a ha).1.
pose c : R := ((k.+1)`!)%:R.
have hc0 : c!= 0 by rewrite /c pnatr_eq0 -lt0n fact_gt0.
pose f t := c^-1*:(F k.+1 0-F k.+1 t).
pose v t := -c*scalar_taylor_weight k t.
have hcf : norm_class_zero (fun t : R^o=>`|t|) NY A f.
  apply: (norm_class_zero_scale hNY _).
  exact (norm_class_zero_subtract hNY (norm_class_zero_constant hNY (F k.+1 0) hO) hc).
have hcv : norm_class_zero (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A v.
  exact (@norm_class_zero_scale R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) A (scalar_taylor_weight k) (-c)
    (@scalar_taylor_weight_continuous R A k hO)).
have hD a ha := @taylor_power_integrator_differential R A a k (hO a ha).
apply: (@normed_stieltjes_differentiable_integrator R Y NY hNY A f
  (fun t=>(1-t)^+k.+1) v 0 1
  (F 0%N 1-\sum_(i < k.+2) (((i`!)%:R)^-1*:F i 0))
  ler01 hA hcf hD hcv).2.
have hi := norm_curve_taylor_riemann_remainder hNY hA hF hc.
apply: normed_stieltjes_integral_ext _ _ hi=>t //.
rewrite /f /v scalerA.
have hcoef : (-c*scalar_taylor_weight k t)*c^-1=
    -scalar_taylor_weight k t.
  by rewrite !mulNr mulrAC mulfV // mul1r.
by rewrite hcoef scaleNr -scalerN opprB.
Qed.
