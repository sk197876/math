(** Federer (1969), 3.1.11, pp. 220–221:
    symmetric higher differentials act on the symmetric
    algebra from Chapter 1. The divided powers in
    Taylor's formula are the existing divided powers
    of 1.9.3, p. 42. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom RealNormUP PowerWords
  SymmetricAlgebra SymmetricGrading SymmetricDividedMonomials
  SymmetricForms SymmetricFormWords SymmetricFormExtension
  ContinuousMultilinearUP NormHigherDifferentialUP
  NormHigherDifferentialSymmetricForm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_form_power_evaluation]:
    the evaluation of a symmetric form on a
    product of vectors, Federer 1.10.1, p. 44,
    used for the powers in 3.1.11, p. 221. *)
Lemma symmetric_form_power_evaluation (R : realType) k
    (X Y : lmodType R) (phi : S_m X Y k) v :
  sform_homogeneous phi (symmetric_vector_power v k)=
    phi [tuple v | i<k].
Proof.
rewrite /symmetric_vector_power sform_homogeneousE sform_extensionE.
have he : nseq k v=val [tuple v | i<k].
  have hc (s : seq 'I_k) : [seq v | i<-s]=nseq (size s) v.
    by elim: s=>[|i s ih] //=; rewrite ih.
  change (nseq k v=[seq v | i<-enum 'I_k]).
  by rewrite hc size_enum_ord.
rewrite he; exact: sform_wordsE.
Qed.

(** Source for [norm_higher_differential_symmetric_algebra_exists]:
    Federer 3.1.11, pp. 220–221, interprets
    the differential as a linear functional on
    the appropriate symmetric power. This extension
    is obtained through the sealed Chapter 1
    universal property, and evaluates divided powers
    exactly as in the printed Taylor formula. *)
Theorem norm_higher_differential_symmetric_algebra_exists (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (A : X->Prop) (f : X->Y) a (z : Z k) :
  has_norm_higher_differential NX ez ZN A f k a z ->
  exists H : Hom_m Y (symmetric_grading X) k,
    (forall u : {ffun 'I_k->X},
      H (symmetric_word (power_seq u))=@ez k u z) /\
    forall v, H (symmetric_divided_vector_power v k)=
      ((k`!)%:R)^-1*: @ez k [ffun i : 'I_k=>v] z.
Proof.
move=> hz.
have [phi [he _]] := norm_higher_differential_symmetric_form_exists
  hNX hNY hZ hz.
exists (sform_homogeneous phi); split.
- move=> u; rewrite sform_homogeneousE sform_extensionE.
  change (sform_words phi (val [tuple u i | i<k])=@ez k u z).
  rewrite sform_wordsE he.
  congr (@ez k _ z); by apply/ffunP=>i; rewrite ffunE tnth_mktuple.
- move=> v; rewrite /symmetric_divided_vector_power linearZ.
  change (((k`!)%:R)^-1*:sform_homogeneous phi (symmetric_vector_power v k)=
    ((k`!)%:R)^-1*: @ez k [ffun i : 'I_k=>v] z).
  rewrite symmetric_form_power_evaluation he.
  congr (_*: @ez k _ z); by apply/ffunP=>i; rewrite !ffunE tnth_mktuple.
Qed.
