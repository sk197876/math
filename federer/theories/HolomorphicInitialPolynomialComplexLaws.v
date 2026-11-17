(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    every original leading polynomial is analytic on
    the whole finite-dimensional source. Identify its exact
    normalized jet formula with the already proved actual
    polynomial model; do not impose coefficient bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import HomogeneousPolynomialFunctions ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP Hom RealNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm ComplexNormUP InnerNorm HilbertFormCompactness LinearBasis
  PolynomialFunctions NormAnalyticUP HolomorphicGermUP HolomorphicInitialPolynomialUP
  HolomorphicNormalizedJetPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_initial_polynomial_complex_homogeneous]: the
    finite family's actual homogeneous polynomial equations
    are complex homogeneous of their actual degree, as required
    in 3.4.12, p. 339. Homogeneity follows from the original
    polynomial formula and finite source dimension. *)
Theorem holomorphic_initial_polynomial_complex_homogeneous (R:realType) (X:lmodType (ComplexScalars.C R))
    (B:X->X->ComplexScalars.C R) (hB:is_hermitian_product B) n (e:'I_n->X) (he:is_basis e)
    (alpha:holomorphic_germ_space (complex_norm_real (hermitian_complex_norm hB)) (0:X)) k (P:X->ComplexScalars.C R):
  is_initial_holomorphic_germ_polynomial alpha k P ->
  @is_homogeneous_polynomial (ComplexScalars.C R) X (ComplexScalars.C R)^o k P.
Proof.
move=>hInitial.
have [Q [hPolynomial [hAnalytic hFormula]]]:=@holomorphic_normalized_jet_polynomial_exists R X B hB n e he k alpha.
have hEqual:P=(fun x=>Q x).
  apply:funext=>x;by rewrite hInitial.2.2.2 hFormula.
by rewrite hEqual.
Qed.
