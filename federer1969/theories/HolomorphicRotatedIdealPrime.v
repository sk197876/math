(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 329: original unitary pullback preserves prime ideals.
    Reuse the actual inverse-membership, properness and ideal laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology UnitaryGroup HolomorphicGermUP HolomorphicGermRing CommutativeIdealUP
  AnalyticRotatedIdealUP AnalyticRotatedIdealSealed AnalyticIdealImageLaws
  HolomorphicUnitaryPullback HolomorphicUnitaryPullbackInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import CommutativeIdealUP HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackInverse.
Section PrimeImage.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Hypothesis hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->restricted_space (ComplexScalars.embed R) X.
Hypothesis he:is_basis e.
Local Notation O:=(@unitary_group R X H hH n e he).
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation M:=(fun g:O=>@holomorphic_unitary_germ_map R X H hH n e he g).

(** Source for [holomorphic_rotated_germ_ideal_prime]: the original
    rotated ideal is prime whenever the given ideal is prime,
    3.4.12, p. 339. *)
Theorem holomorphic_rotated_germ_ideal_prime (I:set G) (g:O):
  is_prime_commutative_ideal I ->
    is_prime_commutative_ideal (@holomorphic_rotated_germ_ideal R X H hH n e he I g).
Proof.
move=>hPrime;split.
- exact:(@holomorphic_rotated_germ_ideal_is_ideal R X H hH n e he I g hPrime.1).
split.
- exact:(@holomorphic_rotated_germ_ideal_proper R X H hH n e he I g hPrime.2.1).
have [h [hLeft hRight]]:=@holomorphic_unitary_germ_inverse_exists R X H hH n e he g.
have hMember:=@holomorphic_rotated_germ_ideal_inverse_membership R X H hH n e he I g h hLeft hRight.
move=>alpha beta /hMember hProduct.
rewrite rmorphM in hProduct.
have [hAlpha|hBeta]:=hPrime.2.2 _ _ hProduct.
- left;exact:(hMember alpha).2 hAlpha.
- right;exact:(hMember beta).2 hBeta.
Qed.
End PrimeImage.
