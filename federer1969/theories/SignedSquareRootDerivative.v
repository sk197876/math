(** Federer (1969), 3.2.7, p. 246:
    actual derivatives of the signed square-root parameter
    off zero. Use the project's algebraic square-root
    differential and scalar chain and scaling rules. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialScalar NormHigherCurveDerivativeUP
  NormedCurveDerivativeUP ScalarSquareRootDifferential RealCurveDerivativeUP RealCurveDerivativeAlgebra
  ScalarAbsoluteValueCurve LocalRealDerivativeAgreement SignedSquareRootUP SignedSquareRootSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_square_root_real_derivative]:
    supporting actual scalar derivative in the third
    example of Federer 3.2.7, p. 246.
    It is derived from the proved epsilon differential,
    rather than imported from an external calculus. *)
Lemma positive_square_root_real_derivative (R:realType) (a:R):
  0<a -> has_real_curve_derivative Num.sqrt a (2*Num.sqrt a)^-1.
Proof.
move=>ha.
have hD:=scalar_square_root_differential ha.
have hCurve:=(@norm_differential_real_source R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)
  (fun t=>0<t) Num.sqrt a (@scalar_coefficient_linear_map R R^o ((2*Num.sqrt a)^-1))).1 hD.
have hh:=hCurve.2.
change (has_normed_curve_derivative (fun t:R^o=>`|t|) Num.sqrt a (1*(2*Num.sqrt a)^-1)) in hh.
rewrite mul1r in hh; exact ((scalar_normed_curve_derivative _ _ _).1 hh).
Qed.

(** Source for [signed_root_actual_derivative]: the
    actual derivative 1/(2 sqrt(|x|)) off zero,
    supporting both the reparameterization and the
    integrable weight in Federer 3.2.7, p. 246.
    No derivative value is assigned at zero. *)
Theorem signed_root_actual_derivative (R:realType) (x:R):
  x!=0 -> has_real_curve_derivative (@SignedSquareRoot.value R) x (2*Num.sqrt `|x|)^-1.
Proof.
move=>hx0; have ht:=@SignedSquareRoot.laws R.
case:(ltP 0 x)=>hx.
- rewrite (ger0_norm (ltW hx)).
  have hd:0<x/2 by rewrite divr_gt0.
  apply:(@real_derivative_neighbourhood_agreement R Num.sqrt (@SignedSquareRoot.value R)
    x (x/2) ((2*Num.sqrt x)^-1) hd _ (positive_square_root_real_derivative hx)).
  move=>y; rewrite ltr_norml=>/andP[hl hu].
  have hy:0<=y by lra.
  by rewrite (signed_square_root_nonnegative ht hy).
- have hxNeg:x<0 by rewrite lt_neqAle hx0 hx.
  rewrite (ler0_norm (ltW hxNeg)).
  have hNeg:has_real_curve_derivative (fun y:R=> -y) x (-1).
    have he:(fun y:R=>(-1)*y)=(fun y:R=> -y) by apply:funext=>y; rewrite mulN1r.
    by rewrite -he; exact (scalar_slope_actual_derivative (-1) x).
  have hRoot:=positive_square_root_real_derivative (ltac:(by rewrite oppr_gt0; exact hxNeg):0< -x).
  have hCompose:=real_curve_derivative_compose hNeg hRoot.
  have hScale:=real_curve_derivative_scale (-1) hCompose.
  rewrite !mulN1r opprK in hScale.
  have hd:0<(-x)/2 by rewrite divr_gt0 // oppr_gt0.
  apply:(@real_derivative_neighbourhood_agreement R (fun y:R=>(-1)*Num.sqrt (-y)) (@SignedSquareRoot.value R)
    x ((-x)/2) ((2*Num.sqrt (-x))^-1) hd _ hScale).
  move=>y; rewrite ltr_norml=>/andP[hl hu].
  have hy:y<=0 by lra.
  by rewrite mulN1r (signed_square_root_nonpositive ht hy).
Qed.
