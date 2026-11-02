(** Federer (1969), 1.8.2, p. 39: H=B+iA, where B is a real inner product
    and A is an alternating bilinear form. The proofs use only the Hermitian
    specification and sealed complex scalar laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP ScalarRestriction ComplexScalarUP ComplexScalarSealed
  ComplexScalarLaws ComplexCoefficientAlgebra HermitianUP InnerProductUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Parts.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation re := (@ComplexScalars.re R).
Local Notation im := (@ComplexScalars.im R).
Variable V : lmodType C.
Local Notation VR := (restricted_space embed V).
Variable H : V -> V -> C.
Hypothesis hH : is_hermitian_product H.

(** Source for [hermitian_real_part]: Federer 1.8.2, p. 39,
    B in the decomposition H=B+iA, regarded on the underlying real space. *)
Definition hermitian_real_part (v w : VR) : R := re (H v w).

(** Source for [hermitian_imaginary_part]: Federer 1.8.2,
    p. 39, A in the same decomposition. *)
Definition hermitian_imaginary_part (v w : VR) : R := im (H v w).

(** Source for [hermitian_real_part_bilinear]: Federer 1.8.2,
    p. 39, supporting real bilinearity of B, obtained by projection. *)
Lemma hermitian_real_part_bilinear :
  @bilinear R VR VR R^o hermitian_real_part.
Proof.
split=> x a y z; rewrite /hermitian_real_part.
- rewrite (proj1 (hermitian_real_bilinear hH)).
  change (re (embed a * H y x + H z x) = a * re (H y x) + re (H z x)).
  by rewrite (complex_re_add (ComplexScalars.laws R)) (complex_re_scale (ComplexScalars.laws R)).
- rewrite (proj2 (hermitian_real_bilinear hH)).
  change (re (embed a * H x y + H x z) = a * re (H x y) + re (H x z)).
  by rewrite (complex_re_add (ComplexScalars.laws R)) (complex_re_scale (ComplexScalars.laws R)).
Qed.

(** Source for [hermitian_imaginary_part_bilinear]: Federer 1.8.2,
    p. 39, supporting real bilinearity of A. *)
Lemma hermitian_imaginary_part_bilinear :
  @bilinear R VR VR R^o hermitian_imaginary_part.
Proof.
split=> x a y z; rewrite /hermitian_imaginary_part.
- rewrite (proj1 (hermitian_real_bilinear hH)).
  change (im (embed a * H y x + H z x) = a * im (H y x) + im (H z x)).
  by rewrite (complex_im_add (ComplexScalars.laws R)) (complex_im_scale (ComplexScalars.laws R)).
- rewrite (proj2 (hermitian_real_bilinear hH)).
  change (im (embed a * H x y + H x z) = a * im (H x y) + im (H x z)).
  by rewrite (complex_im_add (ComplexScalars.laws R)) (complex_im_scale (ComplexScalars.laws R)).
Qed.

(** Source for [hermitian_real_part_symmetric]: Federer 1.8.2,
    p. 39, conjugate symmetry makes the real part symmetric. *)
Lemma hermitian_real_part_symmetric : forall v w, hermitian_real_part v w = hermitian_real_part w v.
Proof. move=> v w; by rewrite /hermitian_real_part (hermitian_conjugate_symmetric hH) re_conjugate. Qed.

(** Source for [hermitian_imaginary_part_skew]: Federer 1.8.2,
    p. 39, conjugate symmetry negates the imaginary part when arguments switch. *)
Lemma hermitian_imaginary_part_skew v w :
  hermitian_imaginary_part w v = -hermitian_imaginary_part v w.
Proof. by rewrite /hermitian_imaginary_part (hermitian_conjugate_symmetric hH) im_conjugate. Qed.

(** Source for [hermitian_imaginary_diagonal_zero]: Federer 1.8.2,
    p. 39, the imaginary bilinear form is alternating. *)
Lemma hermitian_imaginary_diagonal_zero v : hermitian_imaginary_part v v = 0.
Proof.
have h := hermitian_imaginary_part_skew v v.
have hh : (2 : R) * hermitian_imaginary_part v v = 0.
  by rewrite mulr_natl mulr2n {1}h addNr.
move/eqP: hh; rewrite mulf_eq0 pnatr_eq0 /= => /eqP; exact.
Qed.

(** Source for [hermitian_real_inner_product]: Federer 1.8.2,
    p. 39, the assertion that B is an inner product. *)
Theorem hermitian_real_inner_product : is_inner_product hermitian_real_part.
Proof.
constructor; first exact: hermitian_real_part_bilinear.
- exact: hermitian_real_part_symmetric.
- move=> v; have [->|hv] := eqVneq v 0.
  + by rewrite /hermitian_real_part (bil0l (hermitian_real_bilinear hH)) re_zero ltxx.
  + have hp := hermitian_positive hH hv.
    by rewrite /hermitian_real_part hp.
Qed.

(** Source for [hermitian_imaginary_rotation]: Federer 1.8.2,
    p. 40, first-degree proof: A(v,w)=B(i v,w). *)
Lemma hermitian_imaginary_rotation v w :
  hermitian_imaginary_part v w = hermitian_real_part (ii *: v) w.
Proof.
rewrite /hermitian_real_part (hermitian_conjugate_symmetric hH)
  re_conjugate (hermitian_i_right hH) re_i_mul.
exact: (hermitian_imaginary_part_skew w v).
Qed.
End Parts.
