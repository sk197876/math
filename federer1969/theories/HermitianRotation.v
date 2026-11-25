(** Federer (1969), 1.8.2, pp. 39-40: the real inner-product space carries
    the rotation J(v)=iv, and its associated alternating two-form is
    A(v,w)=B(Jv,w). The lemmas below connect these objects with the existing
    inner-product and exterior-algebra interfaces. Source context:
    HermitianUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ScalarRestriction ComplexScalarUP ComplexScalarSealed
  HermitianUP HermitianRealImaginary HermitianComplexLinearity BilinearTwoForm
  InnerProductUP InnerNorm OrthogonalMaps AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Rotation.
Variable R : rcfType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable H : V -> V -> C.
Hypothesis hH : is_hermitian_product H.

(** Source for [hermitian_rotation]: Federer 1.8.2,
    p. 40, multiplication by i considered as a real endomorphism. *)
Definition hermitian_rotation (v : VR) : VR := (ii *: (v : V) : V).

(** Source for [hermitian_rotation_linear]: Federer 1.8.2,
    pp. 39-40, supporting real linearity of multiplication by i. *)
Lemma hermitian_rotation_linear : linear hermitian_rotation.
Proof.
move=> a v w; change (ii *: (embed a *: v+w) = embed a *: (ii *: v)+ii *: w).
by rewrite scalerDr !scalerA mulrC.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R VR VR *:%R
  hermitian_rotation hermitian_rotation_linear.

(** Source for [hermitian_rotation_square]: Federer 1.8.2,
    p. 39, supporting real operator identity J squared equals minus identity. *)
Lemma hermitian_rotation_square v : hermitian_rotation (hermitian_rotation v) = -v.
Proof. by rewrite /hermitian_rotation scalerA (complex_i_square (ComplexScalars.laws R)) scaleN1r. Qed.

(** Source for [hermitian_rotation_orthogonal]: Federer 1.8.2,
    pp. 39-40, the real rotation preserves the induced inner product. *)
Theorem hermitian_rotation_orthogonal : is_orthogonal_map
  (hermitian_real_part H) (hermitian_real_part H) hermitian_rotation.
Proof. move=> v w; exact: hermitian_rotation_isometry. Qed.

(** Source for [hermitian_rotation_norm]: Federer 1.8.2,
    p. 40, the vector iv has the same Euclidean norm as v. *)
Lemma hermitian_rotation_norm v :
  inner_norm (hermitian_real_inner_product hH) (hermitian_rotation v) =
  inner_norm (hermitian_real_inner_product hH) v.
Proof. exact: orthogonal_map_norm hermitian_rotation_orthogonal v. Qed.

(** Source for [hermitian_two_form]: Federer 1.8.2,
    p. 39, the imaginary part A as an alternating real two-form. *)
Definition hermitian_two_form : A_m VR R^o 2 :=
  @bilinear_two_form R VR R^o (hermitian_imaginary_part H)
    (hermitian_imaginary_part_bilinear hH) (hermitian_imaginary_diagonal_zero hH).

(** Source for [hermitian_two_formE]: Federer 1.8.2,
    pp. 39-40, the evaluation identity A(v,w)=B(iv,w). *)
Theorem hermitian_two_formE v w : hermitian_two_form [tuple v; w] =
  hermitian_real_part H (hermitian_rotation v) w.
Proof. rewrite /hermitian_two_form bilinear_two_formE; exact: hermitian_imaginary_rotation. Qed.
End Rotation.
