(** Federer (1969), 3.1.11, p. 223: the symmetric
    forms representing the actual differentials of scalar inversion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom HomogeneousHom RealNormUP SymmetricAlgebra
  SymmetricForms SymmetricFormWords SymmetricFormExtension SymmetricFunctionalProduct
  SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials
  ContinuousMultilinearUP NormHigherSymmetricFormUP ScalarReciprocalHigherDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_reciprocal_form]: the jth differential
    of y mapped to 1/y, as a symmetric scalar j-form,
    used in Federer 3.1.11, p. 223. *)
Definition scalar_reciprocal_form (R : realType) (a : R) j : S_m R^o R^o j :=
  scalar_reciprocal_derivative_coefficient j a*:
    symmetric_functional_product_form (linear_id R^o) j.

(** Source for [scalar_reciprocal_form_actual]: the displayed
    scalar form represents the actual recursive differential,
    not only a candidate coefficient, Federer 3.1.11, p. 223. *)
Lemma scalar_reciprocal_form_actual (R : realType)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@ev i) (@ZN i)) a j :
  a!=0 -> is_norm_higher_differential_form (fun t : R^o=>`|t|) ev ZN
    (fun t=>t!=0) (fun t=>t^-1) j a (scalar_reciprocal_form a j).
Proof.
move=>ha; have [z [hz he]] := scalar_reciprocal_higher_differentials hZ j ha.
exists z; split; first exact hz.
move=>u; rewrite he /scalar_reciprocal_form sform_scaleE symmetric_functional_product_formE.
change ((\prod_(i<j) u i)*scalar_reciprocal_derivative_coefficient j a=
  scalar_reciprocal_derivative_coefficient j a*\prod_(i<j) tnth [tuple u l | l<j] i).
have ht : (\prod_(i<j) tnth [tuple u l | l<j] i)=\prod_(i<j) u i.
  by apply: eq_bigr=>i _; rewrite tnth_mktuple.
by rewrite ht mulrC.
Qed.

(** Source for [scalar_reciprocal_form_word]: on a symmetric
    word of the correct degree, the outer derivative evaluates
    as (-1)^j j! a^(-j-1) times the product of the word's
    scalar entries, Federer 3.1.11, p. 223. *)
Lemma scalar_reciprocal_form_word (R : realType) (a : R) j (s : seq R^o) :
  size s=j -> sform_homogeneous (scalar_reciprocal_form a j) (symmetric_word s)=
    scalar_reciprocal_derivative_coefficient j a*\prod_(x <- s) x.
Proof.
move=>hs.
pose t : j.-tuple R^o := Tuple (introT eqP hs).
change (sform_homogeneous (scalar_reciprocal_form a j) (symmetric_word t)=
  scalar_reciprocal_derivative_coefficient j a*\prod_(x <- t) x).
rewrite sform_homogeneousE sform_extensionE sform_wordsE /scalar_reciprocal_form
  sform_scaleE symmetric_functional_product_formE.
change (scalar_reciprocal_derivative_coefficient j a*(\prod_(i<j) tnth t i)=
  scalar_reciprocal_derivative_coefficient j a*(\prod_(x <- t) x)).
by rewrite big_tuple.
Qed.

(** Source for [scalar_reciprocal_form_monomial]: substituting
    the inner jet monomial into the outer reciprocal derivative
    produces its scalar monomial, Federer 3.1.11, p. 223. *)
Lemma scalar_reciprocal_form_monomial (R : realType) (a : R) k
    (x : 'I_k->R^o) (alpha : symmetric_multi_index k) :
  sform_homogeneous (scalar_reciprocal_form a (symmetric_multi_degree alpha))
    (symmetric_monomial x alpha)=
  scalar_reciprocal_derivative_coefficient (symmetric_multi_degree alpha) a*
    symmetric_scalar_monomial x alpha.
Proof.
rewrite /symmetric_monomial (scalar_reciprocal_form_word a (symmetric_monomial_word_size x alpha)).
congr (_*_).
rewrite /symmetric_monomial_word /symmetric_scalar_monomial -big_enum.
have hrep n y : (\prod_(z <- nseq n y) z : R)=y^+n.
  by elim:n=>[|n ih]; rewrite /= ?big_nil ?big_cons ?expr0 ?exprS ?ih.
elim:(enum 'I_k)=>[|i s ih]; first by rewrite /= !big_nil.
by rewrite /= big_cat big_cons hrep ih.
Qed.
