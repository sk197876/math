(** Federer (1969), 4.1.25, p. 383: the
    normalized differential summand has exactly the
    original source-vector mass. In particular its size
    does not become unbounded as a positive Jacobian
    tends to zero. Keep the original nonzero-Jacobian
    partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentCoefficientNorms
  EuclideanLinearJacobian CurrentTopImageMass
  PartialFunctionUP CurrentAreaNormalisedImageUP
  CurrentAreaNormalisedImageSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_area_normalised_image_mass]:
    the size of the original vector summand in
    Federer 4.1.25, p. 383. This is a pointwise
    graph law, not a redefinition on exceptional points. *)
Theorem current_area_normalised_image_mass (R : realType)
    (h2 : (1+1 : R) != 0) m n
    (f : R_n R m -> R_n R n)
    (xi : R_n R m -> exterior_power (R_n R m) m) x v :
  partial_function_graph (@CurrentAreaNormalisedImage.value R m n f xi) x v ->
  @current_vector_mass R h2 n m v = @current_vector_mass R h2 m m (xi x).
Proof.
move=> hValue.
have [D [_ [hNonzero hFormula]]] :=
  (@CurrentAreaNormalisedImage.laws R m n f xi x v).1 hValue.
rewrite -hFormula /current_area_normalised_image_coefficient
  (real_seminorm_scale (@current_vector_mass_real_norm R h2 n m).1)
  current_top_image_mass.
have hPositive : 0 < euclidean_linear_jacobian m D.
  by rewrite lt_def hNonzero euclidean_linear_jacobian_nonnegative.
have hInverse : 0 <= (euclidean_linear_jacobian m D)^-1.
  by rewrite invr_ge0; exact: ltW hPositive.
by rewrite (ger0_norm hInverse) mulrA mulVf // mul1r.
Qed.
