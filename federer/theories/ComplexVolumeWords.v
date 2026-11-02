(** Federer (1969), 1.6.6, p. 27: both displayed volume identities, first
    interleaving each form and its conjugate, then separating the
    holomorphic and conjugate blocks. The identities below hold for any
    finite family of complex-valued real one-forms; a dual complex basis is
    a special case. Empty families are included. Source context are recorded
    in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra binomial.
From Federer Require Import AlternatingCoordinates WordEvaluation PairedGradedWords
  AlgebraUP GradedAlgebra ComplexScalarUP ComplexScalarSealed ComplexCharacteristic
  ComplexCoefficientAlgebra ComplexFormConjugation ComplexFormProducts
  ComplexConjugateProducts ComplexAlgebraScalars TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Volume.
Variable R : realFieldType.
Hypothesis hR : (1+1 : R) != 0.
Variable U : lmodType R.
Local Notation C := (ComplexScalars.C R).
Local Notation CR := (complex_real_algebra R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation A := (alternating_unital_algebra hR U CR).
Local Notation F := (A_m U CR 1).
Local Notation mul := (alg_mul A).

(** Source for [complex_one_form_word]: Federer 1.6.6,
    p. 27, displayed volume products. The ordered alternating product
    of a sequence of one-forms, with the empty product equal to one. *)
Definition complex_one_form_word (s : seq F) : A :=
  @word_eval R (Choice.clone F _) A (@form_include R U CR 1) s.

(** Source for [complex_pair_volume]: Federer 1.6.6, p. 27,
    first displayed volume identity, for one pair. The real and
    imaginary parts satisfy sigma wedge tau=(i/2) alpha wedge bar(alpha). *)
Lemma complex_pair_volume (a : F) :
  form_wedge hR (alg_bilinear CR)
    (embed_real_form (real_part_form a)) (embed_real_form (imaginary_part_form a)) =
  complex_scale_form (ii / (1+1))
    (form_wedge hR (alg_bilinear CR) a (conjugate_form a)).
Proof.
rewrite (conjugate_product_odd hR (m:=1) (erefl true) a)
  complex_scale_formA imaginary_half_cancels complex_scale_form1.
by [].
Qed.

(** Source for [complex_pair_volume_included]: Federer
    1.6.6, p. 27, first displayed volume identity. The one-pair
    calculation in the full alternating algebra. *)
Lemma complex_pair_volume_included (a : F) :
  mul (form_include (embed_real_form (real_part_form a)))
      (form_include (embed_real_form (imaginary_part_form a))) =
  complex_algebra_scale (h2:=hR) (ii / (1+1)) (mul (form_include a) (form_include (conjugate_form a))).
Proof.
change (alternating_wedge hR (alg_bilinear CR)
    (form_include (embed_real_form (real_part_form a)))
    (form_include (embed_real_form (imaginary_part_form a))) =
  complex_algebra_scale (h2:=hR) (ii / (1+1))
    (mul (form_include a) (form_include (conjugate_form a)))).
rewrite -(form_wedge_include hR (alg_bilinear CR)
  (embed_real_form (real_part_form a)) (embed_real_form (imaginary_part_form a)))
  complex_pair_volume complex_form_scale_include form_wedge_include.
by [].
Qed.

(** Source for [complex_volume_interleaved]: Federer 1.6.6,
    p. 27, first displayed volume identity. For n one-forms the real
    paired product is (i/2)^n times the product of alpha_j,bar(alpha_j)
    in interleaved order. This includes n=0. *)
Theorem complex_volume_interleaved (s : seq F) :
  complex_one_form_word (flatten [seq [:: embed_real_form (real_part_form a);
      embed_real_form (imaginary_part_form a)] | a <- s]) =
  complex_algebra_scale (h2:=hR) ((ii / (1+1))^+(size s))
    (complex_one_form_word (flatten [seq [:: a; conjugate_form a] | a <- s])).
Proof.
elim: s => [|a s ih]; first by rewrite /= expr0 complex_algebra_scale1.
change (mul (form_include (embed_real_form (real_part_form a)))
  (mul (form_include (embed_real_form (imaginary_part_form a)))
    (complex_one_form_word (flatten [seq [:: embed_real_form (real_part_form b);
      embed_real_form (imaginary_part_form b)] | b <- s]))) =
  complex_algebra_scale (h2:=hR) ((ii / (1+1))^+(size s).+1)
    (mul (form_include a) (mul (form_include (conjugate_form a))
      (complex_one_form_word (flatten [seq [:: b; conjugate_form b] | b <- s]))))).
rewrite !(@alg_assoc R A) complex_pair_volume_included ih
  complex_algebra_scale_product exprS.
by [].
Qed.

(** Source for [complex_conjugate_blocks]: Federer 1.6.6,
    p. 27, second displayed volume identity. Reordering the interleaved
    complex/conjugate product into two blocks contributes binomial(n,2)
    sign changes; paired_word_sign_exponent identifies this with n(n-1)/2. *)
Lemma complex_conjugate_blocks (s : seq F) :
  complex_one_form_word (flatten [seq [:: a; conjugate_form a] | a <- s]) =
  (-1 : R)^+'C(size s,2) *:
    mul (complex_one_form_word s) (complex_one_form_word [seq conjugate_form a | a <- s]).
Proof.
have hm : graded_product (A_star_grading U CR) mul :=
  alternating_wedge_graded hR (alg_bilinear CR).
have hu : homogeneous (A_star_grading U CR) 0 (alg_one A) :=
  coefficient_form_homogeneous U (alg_one CR).
have hc : graded_anticommutative (A_star_grading U CR) mul :=
  alternating_wedge_anticommutative hR (alg_bilinear CR) (@mulrC C).
have h := @paired_word_interleaving_sign R A (A_star_grading U CR) hm hu hc
  (Choice.clone F _) (@form_include R U CR 1) (@form_include_homogeneous R U CR 1)
  (Choice.clone F _) idfun (@conjugate_form R U 1) s.
by rewrite map_id in h.
Qed.

(** Source for [complex_volume_blocks]: Federer 1.6.6,
    p. 27, second displayed volume identity. The real paired product
    equals (i/2)^n times (-1)^(n(n-1)/2) times the two complex blocks. *)
Theorem complex_volume_blocks (s : seq F) :
  complex_one_form_word (flatten [seq [:: embed_real_form (real_part_form a);
      embed_real_form (imaginary_part_form a)] | a <- s]) =
  complex_algebra_scale (h2:=hR) ((ii / (1+1))^+(size s))
    ((-1 : R)^+((size s * (size s - 1)) %/ 2) *:
      mul (complex_one_form_word s) (complex_one_form_word [seq conjugate_form a | a <- s])).
Proof. by rewrite complex_volume_interleaved complex_conjugate_blocks paired_word_sign_exponent. Qed.
End Volume.
