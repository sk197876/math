(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8), pp. 326,
    329–330: original prefix rings are nested,
    and original polynomials in the next
    coordinate belong to the next prefix
    ring. Apply the existing pointed prefix
    composition and polynomial-image theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP LinearBasis FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness FieldCoordinateFunctional
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermRepresentatives HolomorphicCoordinateGermsSealed
  FieldPrefixCoordinatesSealed HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws HolomorphicPrefixNestedComposition
  HolomorphicPrefixCoordinateGerm HolomorphicPrefixGermSubring HolomorphicPrefixGermSubringLaws
  CommutativeSubringUP CommutativePolynomialUP CommutativePolynomialEvaluationUP PolynomialEvaluationImage
  HolomorphicCoordinateGermsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PrefixPolynomials.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:is_complex_norm NX.
Local Notation hNXR:=(complex_norm_real hNX).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable j:'I_n.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation Y:=(coordinate_space (ComplexScalars.C R) (j:nat).+1).
Local Notation NY:=(@holomorphic_coordinate_norm R (j:nat).+1).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (j:nat).+1)).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) (j:nat))
  (@holomorphic_coordinate_norm R (j:nat))
  (complex_norm_real (@holomorphic_coordinate_norm_laws R (j:nat))) 0)].
Local Notation A1:=[the comNzRingType of (@holomorphic_germ_ring R Y NY hNY 0)].
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation E0:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega (j:nat) hJN).
Local Notation E1:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega (j:nat).+1 (ltn_ord j)).
Local Notation Q1:=(@holomorphic_prefix_germ_subring R X NX hNXR n e he omega (j:nat).+1 (ltn_ord j)).
Local Notation Gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j).

(** Source for [holomorphic_adjacent_prefix_factorisation]:
    original prefix germ pullbacks factor
    through the next prefix, 3.4.8(1),(8),
    pp. 326, 329. Apply the existing
    exact adjacent composition theorem. *)
Theorem holomorphic_adjacent_prefix_factorisation:
  exists F:{rmorphism A->A1},forall a:A,E0 a = E1 (F a).
Proof.
pose covector:=fun i:'I_(j:nat).+1=>@field_coordinate_functional (ComplexScalars.C R) (j:nat).+1 i.
pose P:=@FieldPrefixCoordinates.projection (ComplexScalars.C R) Y (j:nat).+1 covector (j:nat) (leqnSn (j:nat)).
pose F:=@holomorphic_prefix_germ_map R Y NY hNY (j:nat).+1
  (@coordinate_basis (ComplexScalars.C R) (j:nat).+1) (@coordinate_basisP (ComplexScalars.C R) (j:nat).+1) covector (j:nat) (leqnSn (j:nat)).
have hP:=@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) Y (j:nat).+1 covector (j:nat) (leqnSn (j:nat)).
have hF:=@holomorphic_prefix_germ_map_specification R Y NY hNY (j:nat).+1
  (@coordinate_basis (ComplexScalars.C R) (j:nat).+1) (@coordinate_basisP (ComplexScalars.C R) (j:nat).+1) covector (j:nat) (leqnSn (j:nat)).
exists F.
exact:(@holomorphic_adjacent_prefix_germ_composition R X NX hNXR n omega (j:nat) hJN (ltn_ord j)
  (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat) hJN)
  (@FieldPrefixCoordinates.projection (ComplexScalars.C R) X n omega (j:nat).+1 (ltn_ord j)) P E0 E1 F
  (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (j:nat) hJN)
  (@FieldPrefixCoordinates.projection_laws (ComplexScalars.C R) X n omega (j:nat).+1 (ltn_ord j)) hP
  (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega (j:nat) hJN)
  (@holomorphic_prefix_germ_map_specification R X NX hNXR n e he omega (j:nat).+1 (ltn_ord j)) hF).
Qed.

(** Source for [holomorphic_next_prefix_coordinate_member]:
    the next original coordinate germ belongs
    to its original prefix ring, 3.4.8(1),
    p. 326. An actual coordinate representative
    and the checked prefix-coordinate identity
    prove membership. *)
Theorem holomorphic_next_prefix_coordinate_member:Q1 Gamma.
Proof.
pose covector:=fun i:'I_(j:nat).+1=>@field_coordinate_functional (ComplexScalars.C R) (j:nat).+1 i.
have [f hValues]:=@holomorphic_coordinate_representative_exists R Y NY
  (@holomorphic_coordinate_norm_laws R (j:nat).+1) (j:nat).+1
  (@coordinate_basis (ComplexScalars.C R) (j:nat).+1)
  (@coordinate_basisP (ComplexScalars.C R) (j:nat).+1) covector ord_max.
apply/holomorphic_prefix_germ_subring_membership;exists (holomorphic_germ f).
exact:(@holomorphic_prefix_last_coordinate_germ R X NX hNX n e he omega j f hValues).
Qed.

(** Source for [holomorphic_prefix_polynomial_member]: every
    original polynomial in gamma_j with
    coefficients in Q_j belongs to Q_(j+1),
    as used for the original numerator
    in 3.4.8(8), p. 330. Apply the
    existing least polynomial-image subring law. *)
Theorem holomorphic_prefix_polynomial_member (P:comNzRingType)
  (embed:{rmorphism A->P}) (variable:P) (coefficient:P->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (J:{rmorphism P->G}):
  is_commutative_polynomial_evaluation embed variable E0 Gamma J ->forall H:P,Q1 (J H).
Proof.
move=>hJ.
have hImage:=@polynomial_evaluation_image_generated A P G embed variable coefficient hP E0 Gamma J hJ.
have hRing:=@holomorphic_prefix_germ_subring_laws R X NX hNXR n e he omega (j:nat).+1 (ltn_ord j).
have [F hF]:=holomorphic_adjacent_prefix_factorisation.
have hGenerators:(fun a:G=>a = Gamma \/exists b:A,a = E0 b) `<=` Q1.
  move=>a [->|[b ->]];first exact:holomorphic_next_prefix_coordinate_member.
  apply/holomorphic_prefix_germ_subring_membership;exists (F b);exact:esym (hF b).
have hAll:=generated_commutative_subring_minimal hImage hRing hGenerators.
move=>H;apply:hAll;by exists H.
Qed.
End PrefixPolynomials.
