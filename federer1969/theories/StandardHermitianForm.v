(** Federer (1969), 1.8.2, p. 39: the imaginary two-form of the standard
    Hermitian product is (i/2) sum_j z_j wedge conjugate(z_j). The equality
    is in real alternating forms with complex values, embedding the
    real-valued imaginary part on the left. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP AlternatingForms AlternatingProduct ScalarRestriction ComplexScalarUP ComplexScalarSealed
  ComplexScalarLaws ComplexCoefficientAlgebra ComplexCharacteristic
  ComplexFormConjugation FiniteCoordinates StandardHermitian HermitianRotation
  HermitianRealImaginary FormEvaluation OneFormIdentification OneFormLinear
  OneFormCommutator Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section StandardForm.
Variable R : rcfType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation CR := (complex_real_algebra R).
Variable n : nat.
Local Notation E := (coordinate_space C n).
Local Notation ER := (restricted_space embed E).

(** Source for [complex_coordinate_real]: Federer 1.8.2,
    p. 39, the usual complex coordinate function, viewed as real linear. *)
Definition complex_coordinate_real (j : 'I_n) (v : ER) : CR := v j.

(** Source for [complex_coordinate_real_linear]: Federer 1.8.2,
    p. 39, supporting real linearity of the coordinate functions. *)
Lemma complex_coordinate_real_linear j : linear (complex_coordinate_real j).
Proof. by move=> a v w; rewrite /complex_coordinate_real !ffunE. Qed.
HB.instance Definition _ j := GRing.isLinear.Build R ER CR *:%R
  (complex_coordinate_real j) (complex_coordinate_real_linear j).

(** Source for [complex_coordinate_form]: Federer 1.8.2,
    p. 39, z_j as a complex-valued real one-form. *)
Definition complex_coordinate_form j : A_m ER CR 1 :=
  one_form (hom_of_linear
    (GRing.Linear.clone R ER CR *:%R (complex_coordinate_real j) _)).

(** Source for [complex_coordinate_formE]: Federer 1.8.2,
    p. 39, evaluating the coordinate one-form. *)
Lemma complex_coordinate_formE j v : complex_coordinate_form j [tuple v] = v j.
Proof. by rewrite /complex_coordinate_form one_formE hom_of_linearE. Qed.

(** Source for [complex_two_one_formsE]: Federer 1.8.2,
    p. 39, supporting evaluation of the two-factor products in the
    displayed coordinate formula; the product is defined in 1.4.2, pp. 18-19. *)
Lemma complex_two_one_formsE (a b : A_m ER CR 1) v w :
  form_wedge (real_two_nonzero R) (alg_bilinear CR) a b [tuple v; w] =
    a [tuple v] * b [tuple w] - a [tuple w] * b [tuple v].
Proof.
have h := @one_forms_wedge_two R (real_two_nonzero R) ER CR _
  (alg_bilinear CR) (one_hom a) (one_hom b) v w.
rewrite /one_generator !one_homK !one_homE in h.
exact h.
Qed.

(** Source for [imaginary_conjugate_difference]: Federer 1.8.2,
    p. 39, scalar identity supporting the factor i/2 in the coordinate
    formula: (i/2)(conjugate z-z) is the embedded imaginary part of z. *)
Lemma imaginary_conjugate_difference (z : C) :
  ii / (1+1) * (conjugate z-z) = embed (ComplexScalars.im z).
Proof.
have hd : conjugate z-z = (-(1+1)*ii) * embed (ComplexScalars.im z).
  rewrite {1}(complex_decomposition (ComplexScalars.laws R) (conjugate z))
    re_conjugate im_conjugate rmorphN mulrN.
  rewrite [X in _ - X = _](complex_decomposition (ComplexScalars.laws R) z).
  rewrite opprD addrACA subrr add0r.
  by rewrite !mulNr !mulrDl !mul1r opprD.
by rewrite hd mulrA imaginary_half_cancels mul1r.
Qed.

(** Source for [standard_hermitian_two_form_coordinates]: Federer 1.8.2,
    p. 39, the displayed formula A=(i/2) sum_j z_j wedge conjugate(z_j).
    It also covers nu=0, when both sides are zero. *)
Theorem standard_hermitian_two_form_coordinates :
  embed_real_form (hermitian_two_form (@standard_hermitian_productP R n)) =
  complex_scale_form (ii / (1+1))
    (\sum_j form_wedge (real_two_nonzero R) (alg_bilinear CR)
      (complex_coordinate_form j) (conjugate_form (complex_coordinate_form j))).
Proof.
apply: form_ext => /tupleP [v t]; case/tupleP: t => w t; rewrite (tuple0 t).
rewrite embed_real_formE hermitian_two_formE complex_scale_formE
  -(@hermitian_imaginary_rotation R E _ (@standard_hermitian_productP R n)).
change (embed (complex_imaginary_part
  (\sum_j (conjugate (v j)*w j : CR))) =
  ii / (1+1) * form_evaluate [tuple v; w]
    (\sum_j form_wedge (real_two_nonzero R) (alg_bilinear CR)
      (complex_coordinate_form j) (conjugate_form (complex_coordinate_form j)))).
rewrite !linear_sum rmorph_sum mulr_sumr; apply: eq_bigr => j _.
change (embed (ComplexScalars.im (conjugate (v j)*w j)) =
  ii/(1+1) * (form_wedge (real_two_nonzero R) (alg_bilinear CR)
    (complex_coordinate_form j) (conjugate_form (complex_coordinate_form j)) [tuple v; w])).
rewrite complex_two_one_formsE !conjugate_formE !complex_coordinate_formE.
have hc : conjugate (conjugate (v j)*w j) = v j*conjugate (w j).
  by rewrite conjugate_mul conjugateK.
rewrite -hc [w j * conjugate (v j)]mulrC.
exact: esym (imaginary_conjugate_difference (conjugate (v j)*w j)).
Qed.
End StandardForm.
