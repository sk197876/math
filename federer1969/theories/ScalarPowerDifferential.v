(** Federer (1969), 3.1.11, pp. 220–222:
    finite-power differentiation, supporting polynomial
    Taylor weights and the scalar Leibniz calculus. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialLocal NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_power_derivative_coefficient]:
    the elementary recurrence for differentiating a
    scalar power, used for the polynomial terms
    in Federer 3.1.11, pp. 220–222. *)
Lemma scalar_power_derivative_coefficient (R : realType) (a l : R) n :
  (n%:R*a^+n.-1* l)*a+a^+n* l=n.+1%:R*a^+n* l.
Proof.
have hcast j : (j.+1%:R : R)=j%:R+1 by rewrite -addn1 natrD natr1.
case: n=>[|n]; first by rewrite expr0 !mul0r add0r !mul1r.
rewrite [n.+2%:R]hcast /= exprS; ring.
Qed.

(** Source for [norm_curve_power_differential]:
    the first derivative of a finite scalar power,
    supporting the polynomial calculus in Federer
    3.1.11, pp. 220–222. The zero power
    has derivative zero at every interior domain point. *)
Theorem norm_curve_power_differential (R : realType)
    (A : R->Prop) (f : R->R) a l n :
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A f a (@scalar_coefficient_linear_map R R^o l) ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun t=>f t^+n) a
    (@scalar_coefficient_linear_map R R^o (n%:R*f a^+n.-1* l)).
Proof.
move=> hf; elim: n=>[|n ih].
- rewrite !mul0r scalar_coefficient_linear_zero.
  exact (@norm_differential_constant R R^o R^o
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
    A a 1 (norm_differential_interior hf)).
- have hp := norm_curve_scalar_product (@scalar_absolute_value_norm R) ih hf.
  change (has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A (fun t=>f t^+n*f t) a
    (@scalar_coefficient_linear_map R R^o
      ((n%:R*f a^+n.-1* l)*f a+f a^+n* l))) in hp.
  rewrite scalar_power_derivative_coefficient in hp.
  apply: (norm_differential_domain_agreement (@scalar_absolute_value_norm R) _ hp).
  by move=> t ht; rewrite exprSr.
Qed.
