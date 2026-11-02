(** Federer (1969), 3.2.7, p. 246:
    actual polynomial and reciprocal derivatives for
    the oscillatory curve. These adapters reuse the
    project's norm-differential calculus of 3.1.1 and
    3.1.11; no external calculus theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialScalar NormedCurveDerivativeUP
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra ScalarPowerDifferential ScalarReciprocalDifferential
  RealCurveDerivativeUP ScalarAbsoluteValueCurve.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_curve_derivative_full_differential]:
    supporting adapter for the third example of
    Federer 3.2.7, p. 246. A finite actual
    scalar derivative determines its full-source linear differential. *)
Lemma real_curve_derivative_full_differential (R:realType) (f:R->R) (a v:R):
  has_real_curve_derivative f a v ->
  has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    (fun _=>True) f a (@scalar_coefficient_linear_map R R^o v).
Proof.
move=>hD; apply:(@norm_differential_real_source R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)
  (fun _=>True) f a _).2; split.
- exists 1; split; first exact:ltr01; by move=>h _.
- change (has_normed_curve_derivative (fun t:R^o=>`|t|) f a (1*v)).
  rewrite mul1r; exact ((scalar_normed_curve_derivative _ _ _).2 hD).
Qed.

(** Source for [real_curve_derivative_from_differential]:
    actual coefficient of a scalar differential,
    supporting the explicit formulas in Federer
    3.2.7, p. 246. Its surrounding domain
    may be any neighbourhood domain in the differential. *)
Lemma real_curve_derivative_from_differential (R:realType) (A:R->Prop) (f:R->R) (a v:R):
  has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    A f a (@scalar_coefficient_linear_map R R^o v) -> has_real_curve_derivative f a v.
Proof.
move=>hD.
have hCurve:=(@norm_differential_real_source R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)
  A f a _).1 hD.
have hh:=hCurve.2.
change (has_normed_curve_derivative (fun t:R^o=>`|t|) f a (1*v)) in hh.
rewrite mul1r in hh; exact ((scalar_normed_curve_derivative _ _ _).1 hh).
Qed.

(** Source for [real_curve_derivative_product]: supporting
    product rule for the third example of Federer
    3.2.7, p. 246, with actual finite derivatives. *)
Lemma real_curve_derivative_product (R:realType) (f g:R->R) (a v w:R):
  has_real_curve_derivative f a v -> has_real_curve_derivative g a w ->
  has_real_curve_derivative (fun x=>f x*g x) a (v*g a+f a*w).
Proof.
move=>hF hG.
have hP:=norm_curve_scalar_product (@scalar_absolute_value_norm R)
  (real_curve_derivative_full_differential hF) (real_curve_derivative_full_differential hG).
change (has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  (fun _=>True) (fun x=>f x*g x) a
  (@scalar_coefficient_linear_map R R^o (v*g a+f a*w))) in hP.
exact (real_curve_derivative_from_differential hP).
Qed.

(** Source for [real_curve_power_actual_derivative]: supporting
    cube and square derivatives in the third example
    of Federer 3.2.7, p. 246. The zero
    power and zero base remain included. *)
Lemma real_curve_power_actual_derivative (R:realType) (a:R) n:
  has_real_curve_derivative (fun x:R=>x^+n) a (n%:R*a^+n.-1).
Proof.
have hId:has_real_curve_derivative (fun x:R=>x) a 1.
  have he:(fun x:R=>1*x)=(fun x:R=>x) by apply:funext=>x; rewrite mul1r.
  by rewrite -he; exact (scalar_slope_actual_derivative 1 a).
have hP:=norm_curve_power_differential n (real_curve_derivative_full_differential hId).
rewrite mulr1 in hP; exact (real_curve_derivative_from_differential hP).
Qed.

(** Source for [real_curve_reciprocal_actual_derivative]:
    the actual reciprocal derivative away from zero,
    supporting the sine argument in Federer 3.2.7,
    p. 246. The original nonzero domain is retained. *)
Lemma real_curve_reciprocal_actual_derivative (R:realType) (a:R):
  a!= 0 -> has_real_curve_derivative (fun x:R=>x^-1) a (-((a^-1)^+2)).
Proof. move=>ha; exact (real_curve_derivative_from_differential (scalar_reciprocal_differential ha)). Qed.
