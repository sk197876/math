(** Federer (1969), 3.4.12, p. 339: a complex Hermitian
    orthonormal family gives the original paired real orthonormal
    family. Reuse the actual two-block basis of 1.6.6 and the
    real/imaginary identities of 1.8.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws ComplexCoefficientAlgebra
  HermitianUP HermitianRealImaginary HermitianComplexLinearity StandardHermitian ComplexOrderedBases
  LinearBasis FiniteCoordinates OrthonormalFamilies InnerNorm InnerProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [complex_orthonormal_ordered_real_family]: the
    original complex basis yields twice as many orthonormal real
    directions, supporting 3.4.12, p. 339. *)
Theorem complex_orthonormal_ordered_real_family (R:realFieldType)
    (X:lmodType (ComplexScalars.C R)) H (hH:@is_hermitian_product R X H)
    n (e:'I_n->X):
  orthonormal_family H e ->orthonormal_family (hermitian_real_part H) (ordered_real_basis e).
Proof.
move=>hON a b;case:(split_ordP a)=>i ->;case:(split_ordP b)=>j ->;
  rewrite /ordered_real_basis ?(unsplitK (inl _ i)) ?(unsplitK (inl _ j))
    ?(unsplitK (inr _ i)) ?(unsplitK (inr _ j)).
- rewrite eq_lshift /hermitian_real_part hON.
  case:(i==j);first by rewrite -(rmorph1 (ComplexScalars.embed R)) re_embed.
  exact:re_zero.
- rewrite eq_lrshift /hermitian_real_part (hermitian_i_right hH) re_i_mul hON.
  case:(i==j);first by rewrite -(rmorph1 (ComplexScalars.embed R)) im_embed oppr0.
  by rewrite im_zero oppr0.
- rewrite eq_rlshift -(@hermitian_imaginary_rotation R X H hH) /hermitian_imaginary_part hON.
  case:(i==j);first by rewrite -(rmorph1 (ComplexScalars.embed R)) im_embed.
  exact:im_zero.
- rewrite eq_rshift (@hermitian_rotation_isometry R X H hH) /hermitian_real_part hON.
  case:(i==j);first by rewrite -(rmorph1 (ComplexScalars.embed R)) re_embed.
  exact:re_zero.
Qed.
