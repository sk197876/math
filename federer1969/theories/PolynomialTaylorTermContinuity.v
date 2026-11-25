(** Federer (1969), 3.1.11, p. 221:
    the translated coefficient forms S_i(x)
    remain continuous. The contraction formula
    is the one already proved in 1.10.4,
    p. 46, and preserves a finite product bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Bilinear Hom HomogeneousHom Graded GradedComponents
  RealNormUP SymmetricAlgebra SymmetricGrading SymmetricDividedMonomials
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFormIsomorphism
  PolynomialTaylorTerms ContinuousSymmetricFormAdapter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_vector_power_constant_tuple]:
    the power x^m is the symmetric word
    with m equal entries, supporting the
    contraction formula in Federer 3.1.11,
    p. 221, from 1.9.3, p. 42. *)
Lemma symmetric_vector_power_constant_tuple (K : fieldType)
    (X : lmodType K) (x : X) m :
  symmetric_vector_power x m=symmetric_word [tuple x | i<m].
Proof.
rewrite /symmetric_vector_power; congr symmetric_word.
have hh (s : seq 'I_m) : [seq x | i<-s]=nseq (size s) x.
  by elim:s=>[|i s ih] //=; rewrite ih.
change (nseq m x=[seq x | i<-enum 'I_m]).
by rewrite hh size_enum_ord.
Qed.

(** Source for [symmetric_taylor_term_tuple_value]:
    each coefficient contraction is the original
    symmetric form with repeated x arguments,
    divided by the appropriate factorial,
    Federer 1.10.4, p. 46, used
    to prove D^i P=S_i in 3.1.11, p. 221. *)
Lemma symmetric_taylor_term_tuple_value (K : fieldType)
    (X Y : lmodType K) m i (hi : (i<=m)%N)
    (phi : S_m X Y m) x (t : i.-tuple X) :
  symmetric_taylor_term i phi x t=
    (((m-i)`!)%:R)^-1*:
      phi (tcast (subnKC hi) [tuple of t++[tuple x | j<m-i]]).
Proof.
have he : symmetric_taylor_term i phi x t=
    sform_homogeneous (symmetric_taylor_term i phi x) (symmetric_word t).
  by rewrite sform_homogeneousE sform_extensionE sform_wordsE.
have ht : homogeneous (symmetric_grading X) i (symmetric_word t).
  have hh := symmetric_word_homogeneous t; by rewrite size_tuple in hh.
rewrite he (symmetric_taylor_term_pairing _ _ ht)
  /symmetric_divided_vector_power (bilZr (symmetric_product_bilinear X))
  linearZ symmetric_vector_power_constant_tuple symmetric_word_cat
  /= sform_extensionE.
congr (_ *: _); by rewrite -sform_wordsE val_tcast.
Qed.

(** Source for [symmetric_taylor_term_bounded]:
    contraction of a continuous coefficient form
    remains continuous, supporting the polynomial
    statement of Federer 3.1.11, p. 221.
    Above-degree terms are the zero form,
    exactly as in 1.10.4, p. 46. *)
Theorem symmetric_taylor_term_bounded (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    m i (phi : S_m X Y m) x :
  norm_bounded_symmetric_form NX NY phi ->
  norm_bounded_symmetric_form NX NY (symmetric_taylor_term i phi x).
Proof.
move=>[C [hC hb]].
case:(leqP i m)=>[hi|hi].
- pose c := (((m-i)`!)%:R : R)^-1.
  pose D := `|c|*C*(NX x)^+(m-i).
  have hpow : 0<=(NX x)^+(m-i) := exprn_ge0 _ (real_seminorm_nonnegative hNX.1 x).
  exists D; split.
  + exact: mulr_ge0 (mulr_ge0 (normr_ge0 c) hC) hpow.
  + move=>t.
    pose u := tcast (subnKC hi) [tuple of t++[tuple x | j<m-i]].
    have hu : \prod_(j<m) NX (tnth u j)=
        (\prod_(j<i) NX (tnth t j))*(NX x)^+(m-i).
      rewrite -(@big_tuple R 1 *%R X m u predT NX) /u val_tcast /= big_cat
        (@big_tuple R 1 *%R X i t predT NX)
        (@big_tuple R 1 *%R X (m-i) [tuple x | j<m-i] predT NX).
      congr (_*_).
      under eq_bigr do rewrite tnth_mktuple.
      by rewrite prodr_const card_ord.
    rewrite (symmetric_taylor_term_tuple_value hi) (real_seminorm_scale hNY.1).
    have hh := ler_wpM2l (normr_ge0 c) (hb u).
    rewrite hu in hh.
    have halg : `|c|*(C*((\prod_(j<i) NX (tnth t j))*(NX x)^+(m-i)))=
        D*(\prod_(j<i) NX (tnth t j)) by rewrite /D; ring.
    by rewrite halg in hh.
- rewrite (symmetric_taylor_term_above_degree _ x hi).
  exists 0; split; first exact: lexx.
  by move=>t; rewrite sform_zeroE (real_seminorm_zero hNY.1) mul0r.
Qed.
