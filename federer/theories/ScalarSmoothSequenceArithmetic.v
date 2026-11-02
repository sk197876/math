(** Federer (1969), 3.1.11, p. 223:
    affine scalar combinations preserve an
    everywhere-defined smooth derivative sequence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra
  ScalarSmoothSequenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_smooth_sequence_scale]:
    the constant denominator in the second
    smooth function of Federer 3.1.11,
    p. 223, scales all derivative
    coefficients by the same constant. *)
Lemma scalar_smooth_sequence_scale (R : realType) (f : R->R)
    (F : nat->R->R) c :
  is_scalar_smooth_derivative_sequence f F ->
  is_scalar_smooth_derivative_sequence (fun x=>c*f x) (fun k x=>c*F k x).
Proof.
move=> [h0 hF]; split; first by move=>x; rewrite h0.
move=>k a; have hN := @scalar_absolute_value_norm R.
have hh := norm_differential_scale hN hN c (hF k a).
by rewrite -scalar_coefficient_linear_scale in hh.
Qed.

(** Source for [scalar_smooth_affine_derivatives_exists]:
    the argument f(1)-f(x) in the
    printed smooth cutoff has derivatives of
    every order, Federer 3.1.11, p. 223.
    The constant affects only order zero. *)
Theorem scalar_smooth_affine_derivatives_exists (R : realType) (f : R->R)
    (F : nat->R->R) c b :
  is_scalar_smooth_derivative_sequence f F ->
  exists G : nat->R->R,
    is_scalar_smooth_derivative_sequence (fun x=>c+b*f x) G.
Proof.
move=> [h0 hF].
pose G k x := if k is 0%N then c+b*F 0%N x else b*F k x.
exists G; split; first by move=>x; rewrite /G h0.
have hN := @scalar_absolute_value_norm R.
move=>[|k] a.
- have hinterior : norm_domain_interior (fun t : R^o=>`|t|) (fun _=>True) a.
    exists 1; split; first exact: ltr01; by move=>h _.
  have hc := norm_differential_constant hN hN c hinterior.
  have hb := norm_differential_scale hN hN b (hF 0%N a).
  have hh := norm_differential_add hN hc hb.
  by rewrite add0r -scalar_coefficient_linear_scale in hh.
- have hh := norm_differential_scale hN hN b (hF k.+1 a).
  by rewrite -scalar_coefficient_linear_scale in hh.
Qed.
