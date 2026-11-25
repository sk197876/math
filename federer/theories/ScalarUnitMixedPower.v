(** Federer (1969), 4.1.11, p. 365: the scalar
    weight (1-t)^i t^j in the sharp join mass integral.
    Its differential and continuity follow from the
    preceding scalar calculus of 3.1.11, pp. 220–222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialLocal NormDifferentialArithmetic NormHigherCurveDerivativeUP
  NormClassOneUP NormClassOneLaws NormOpenDomainLaws ScalarAffineDifferentials
  ScalarPowerDifferential ScalarCoefficientLinearAlgebra ScalarTaylorWeights.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarUnitMixedPower.
Variable R:realType.
Local Notation N := (fun t:R^o=>`|t|).
Local Notation hN := (@scalar_absolute_value_norm R).
Local Notation Full := (fun _:R=>True).
Local Notation hFull := (fun (t:R) (_:True)=>@norm_full_domain_interior R R^o N t).

(** Source for [scalar_unit_mixed_power]: the original
    scalar time weight in Federer 4.1.11, p. 365,
    with both zero exponents retained. *)
Definition scalar_unit_mixed_power i j (t:R):R:=(1-t)^+i*t^+j.

(** Source for [scalar_unit_mixed_power_derivative]: the
    scalar product-rule coefficient for the original time
    weight, supporting Federer 4.1.11, p. 365. *)
Definition scalar_unit_mixed_power_derivative i j (t:R):R:=
  -(i%:R*(1-t)^+i.-1*t^+j)+j%:R*(1-t)^+i*t^+j.-1.

(** Source for [scalar_unit_left_power_differential]: the
    actual derivative of (1-t)^i, supporting the original
    mass coefficient in Federer 4.1.11, p. 365, by
    the power and chain rules of 3.1.11, pp. 220–222. *)
Lemma scalar_unit_left_power_differential i t:
  has_norm_differential N N Full (fun s=>(1-s)^+i) t
    (@scalar_coefficient_linear_map R R^o (-(i%:R*(1-t)^+i.-1))).
Proof.
have hAffine:=@unit_complement_differential R Full t (hFull t I).
have hPower:=@norm_curve_power_differential R Full (fun s=>1-s) t (-1) i hAffine.
by rewrite mulrN1 in hPower.
Qed.

(** Source for [scalar_unit_right_power_differential]: the
    actual derivative of t^j, including j=0, supporting
    Federer 4.1.11, p. 365, by 3.1.11, pp. 220–222. *)
Lemma scalar_unit_right_power_differential j t:
  has_norm_differential N N Full (fun s:R=>s^+j) t
    (@scalar_coefficient_linear_map R R^o (j%:R*t^+j.-1)).
Proof.
have hAffine:=@scalar_affine_derivative_step R 1 0 Full hFull 0%N t I.
have hEq:(fun s:R=>1*s+0)=(fun s=>s) by apply:funext=>s;rewrite mul1r addr0.
change (has_norm_differential N N Full (fun s=>1*s+0) t
  (@scalar_coefficient_linear_map R R^o 1)) in hAffine.
rewrite hEq in hAffine.
have hPower:=@norm_curve_power_differential R Full (fun s:R=>s) t 1 j hAffine.
by rewrite mulr1 in hPower.
Qed.

(** Source for [scalar_unit_mixed_power_differential]:
    the actual derivative of the exact mixed time
    weight, supporting Federer 4.1.11, p. 365. *)
Theorem scalar_unit_mixed_power_differential i j t:
  has_norm_differential N N Full (scalar_unit_mixed_power i j) t
    (@scalar_coefficient_linear_map R R^o (scalar_unit_mixed_power_derivative i j t)).
Proof.
have hProduct:=@norm_curve_scalar_product R R^o N hN Full
  (fun s=>(1-s)^+i) (fun s:R=>s^+j) t
  (-(i%:R*(1-t)^+i.-1)) (j%:R*t^+j.-1)
  (scalar_unit_left_power_differential i t) (scalar_unit_right_power_differential j t).
have hCoefficient:-(i%:R*(1-t)^+i.-1)*t^+j+(1-t)^+i*(j%:R*t^+j.-1)=
    scalar_unit_mixed_power_derivative i j t by rewrite /scalar_unit_mixed_power_derivative;ring.
change (has_norm_differential N N Full (scalar_unit_mixed_power i j) t
  (@scalar_coefficient_linear_map R R^o
    (-(i%:R*(1-t)^+i.-1)*t^+j+(1-t)^+i*(j%:R*t^+j.-1)))) in hProduct.
by rewrite hCoefficient in hProduct.
Qed.

(** Source for [scalar_unit_mixed_power_continuous]:
    the original time weight is continuous on the whole
    real line, supporting its finite interval integral in
    Federer 4.1.11, p. 365. *)
Theorem scalar_unit_mixed_power_continuous i j:
  norm_class_zero N N Full (scalar_unit_mixed_power i j).
Proof.
exact:(@norm_everywhere_differentiable_class_zero R R^o R^o N N hN Full
  (scalar_unit_mixed_power i j) (fun t=>@scalar_coefficient_linear_map R R^o
    (scalar_unit_mixed_power_derivative i j t))
  (fun t _=>scalar_unit_mixed_power_differential i j t)).
Qed.
End ScalarUnitMixedPower.
