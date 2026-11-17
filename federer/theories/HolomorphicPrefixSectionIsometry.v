(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6),
    p. 328: the actual complex prefix inclusion has its original
    inherited Hermitian norm. Apply the existing real orthogonal
    basis criterion to the original paired real bases. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexCoefficientAlgebra
  HermitianUP HermitianRealImaginary HermitianComplexLinearity StandardHermitian ComplexOrderedBases
  LinearBasis FiniteCoordinates OrthonormalFamilies InnerNorm InnerProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
From Federer Require Import HolomorphicLinear ComplexOrthonormalRealBasis StandardHermitianBasisValues
  HolomorphicCoordinateNorm FieldPrefixCoordinatesUP OrthogonalMaps OrthogonalBasisCriteria.
Section Isometry.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable hON:orthonormal_family H e.
Variable p:nat.
Variable hPN:(p<=n)%N.
Variable S:Hom (coordinate_space (ComplexScalars.C R) p) X.
Variable hS:is_field_prefix_section e hPN S.
Local Notation C:=(ComplexScalars.C R).
Local Notation Y:=(coordinate_space C p).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation BY:=(hermitian_real_part (@standard_hermitian_product R p)).
Local Notation hBY:=(hermitian_real_inner_product (@standard_hermitian_productP R p)).
Local Notation BX:=(hermitian_real_part H).
Local Notation hBX:=(hermitian_real_inner_product hH).

(** Source for [holomorphic_prefix_inclusion_orthogonal]: actual
    complex prefix inclusion preserves the underlying real inner
    product, 3.4.12, p. 339. *)
Lemma holomorphic_prefix_inclusion_orthogonal:
  is_orthogonal_map BY BX (hom_as_linear (complex_hom_real S)).
Proof.
pose f:=fun i:'I_p=>e (widen_ord hPN i).
have hF:orthonormal_family H f.
  move=>i j;rewrite /f hON;by rewrite -val_eqE /= val_eqE.
have hRealF:=@complex_orthonormal_ordered_real_family R X H hH p f hF.
have hRealBasis:=@complex_orthonormal_ordered_real_family R Y (@standard_hermitian_product R p)
  (@standard_hermitian_productP R p) p (@coordinate_basis C p) (@standard_hermitian_basis_orthonormal R p).
apply:(@orthogonal_map_basis_criterion R YR XR BY BX hBY hBX (p+p)
  (ordered_real_basis (@coordinate_basis C p)) (ordered_real_basisP (@coordinate_basisP C p))
  hRealBasis (hom_as_linear (complex_hom_real S))).
have hValues i:complex_hom_real S (ordered_real_basis (@coordinate_basis C p) i)=ordered_real_basis f i.
  case:(split_ordP i)=>j ->;rewrite /ordered_real_basis ?(unsplitK (inl _ j)) ?(unsplitK (inr _ j))
    complex_hom_real_values ?linearZ /= hS;by [].
move=>i j;rewrite !hom_as_linearE !hValues;exact:hRealF.
Qed.

(** Source for [holomorphic_prefix_section_norm]: the exact
    original norm equality for every prefix vector, including the
    empty prefix, 3.4.12, p. 339. *)
Lemma holomorphic_prefix_section_norm (y:Y):
  inner_norm hBX (S y)=@holomorphic_coordinate_norm R p y.
Proof.
exact:(@orthogonal_map_norm R YR XR BY BX hBY hBX (hom_as_linear (complex_hom_real S))
  holomorphic_prefix_inclusion_orthogonal y).
Qed.
End Isometry.
