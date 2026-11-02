(** Federer (1969), 3.1.11, p. 220:
    the polynomial weights (1-t)^i/i! used in
    the one-variable Taylor formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialLocal NormClassOneUP NormClassOneLaws
  NormHigherCurveDerivativeUP NormedPrimitiveCell ScalarCoefficientLinearAlgebra
  ScalarPowerDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_taylor_weight]:
    the polynomial integration-by-parts weight
    (1-t)^i/i! in Federer 3.1.11, p. 220. *)
Definition scalar_taylor_weight (R : realType) (i : nat) (t : R) :=
  (1-t)^+i/(i`!)%:R.

(** Source for [scalar_taylor_weight_zero]:
    the order-zero Taylor weight is one,
    Federer 3.1.11, p. 220. *)
Lemma scalar_taylor_weight_zero (R : realType) (t : R) :
  scalar_taylor_weight 0%N t= 1.
Proof. by rewrite /scalar_taylor_weight fact0 expr0 divr1. Qed.

(** Source for [scalar_taylor_weight_upper]:
    the positive-order weights vanish at t= 1,
    as used in Federer 3.1.11, p. 220. *)
Lemma scalar_taylor_weight_upper (R : realType) i :
  scalar_taylor_weight i.+1 (1 : R)= 0.
Proof. by rewrite /scalar_taylor_weight subrr expr0n mul0r. Qed.

(** Source for [scalar_taylor_weight_lower]:
    the weights at t= 0 are reciprocal factorials,
    giving the coefficients in Federer 3.1.11, p. 220. *)
Lemma scalar_taylor_weight_lower (R : realType) i :
  scalar_taylor_weight i (0 : R)=((i`!)%:R)^-1.
Proof. by rewrite /scalar_taylor_weight subr0 expr1n div1r. Qed.

(** Source for [factorial_successor_ratio]:
    cancellation of the successive factorials in
    the Taylor-weight derivative, supporting Federer
    3.1.11, p. 220. *)
Lemma factorial_successor_ratio (R : realType) i :
  i.+1%:R/((i.+1)`!)%:R=(((i`!)%:R)^-1 : R).
Proof.
have hi : (i.+1%:R : R)!= 0 by rewrite pnatr_eq0.
by rewrite factS natrM invfM mulrA mulfV // mul1r.
Qed.

(** Source for [unit_complement_differential]:
    the affine parameter 1-t has derivative
    minus one, supporting the Taylor weights
    in Federer 3.1.11, p. 220. *)
Lemma unit_complement_differential (R : realType) (A : R->Prop) a :
  norm_domain_interior (fun t : R^o=>`|t|) A a ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun t=>1-t) a
    (@scalar_coefficient_linear_map R R^o (-1)).
Proof.
move=> hA; split=> //.
- exact: scalar_coefficient_linear_bound (@scalar_absolute_value_norm R) (-1).
- move=> e he; exists 1; split; first exact: ltr01.
  move=> h hh hs.
  change (`|(1-(a+h))-(1-a)-h*(-1)|<=e*`|h|).
  have hid : (1-(a+h))-(1-a)-h*(-1)= 0 by ring.
  rewrite hid normr0; exact: mulr_ge0 (ltW he) (normr_ge0 h).
Qed.

(** Source for [scalar_taylor_weight_differential]:
    successive Taylor weights have derivatives
    minus their predecessor, the cancellation used
    in Federer 3.1.11, p. 220. *)
Theorem scalar_taylor_weight_differential (R : realType)
    (A : R->Prop) a i :
  norm_domain_interior (fun t : R^o=>`|t|) A a ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (scalar_taylor_weight i.+1) a
    (@scalar_coefficient_linear_map R R^o (-scalar_taylor_weight i a)).
Proof.
move=> hA.
have hp := @norm_curve_power_differential R A (fun t=>1-t)
  a (-1) i.+1 (unit_complement_differential hA).
have hs := norm_differential_scale (@scalar_absolute_value_norm R)
  (@scalar_absolute_value_norm R) (((i.+1)`!)%:R)^-1 hp.
rewrite -scalar_coefficient_linear_scale in hs.
have hc : (((i.+1)`!)%:R)^-1*(i.+1%:R*(1-a)^+i*(-1))=
    -scalar_taylor_weight i a.
  have hid : (((i.+1)`!)%:R)^-1*(i.+1%:R*(1-a)^+i*(-1))=
      -(i.+1%:R/((i.+1)`!)%:R)*(1-a)^+i by ring.
  rewrite hid factorial_successor_ratio /scalar_taylor_weight; ring.
change (has_norm_differential (fun t : R^o=>`|t|)
  (fun t : R^o=>`|t|) A (fun t=>(((i.+1)`!)%:R)^-1*(1-t)^+i.+1) a
  (@scalar_coefficient_linear_map R R^o
    ((((i.+1)`!)%:R)^-1*(i.+1%:R*(1-a)^+i*(-1))))) in hs.
rewrite hc in hs.
apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R) _ hs).
by move=> t ht; rewrite /scalar_taylor_weight mulrC.
Qed.

(** Source for [scalar_taylor_weight_continuous]:
    continuity of the polynomial weights used
    in the vector Taylor integral of Federer
    3.1.11, p. 220. *)
Lemma scalar_taylor_weight_continuous (R : realType)
    (A : R->Prop) i :
  (forall a, A a -> norm_domain_interior (fun t : R^o=>`|t|) A a) ->
  norm_class_zero (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (scalar_taylor_weight i).
Proof.
move=> hA; case: i=>[|i].
- apply: (@norm_everywhere_differentiable_class_zero R R^o R^o
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    (@scalar_absolute_value_norm R) A (scalar_taylor_weight 0%N) (fun _=>0)).
  move=> a ha; apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R)
    _ (@norm_differential_constant R R^o R^o
      (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
      (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
      A a 1 (hA a ha))).
  by move=> t ht; rewrite scalar_taylor_weight_zero.
- apply: (@norm_everywhere_differentiable_class_zero R R^o R^o
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    (@scalar_absolute_value_norm R) A (scalar_taylor_weight i.+1)
    (fun a=>@scalar_coefficient_linear_map R R^o (-scalar_taylor_weight i a))).
  move=> a ha; exact: scalar_taylor_weight_differential (hA a ha).
Qed.
