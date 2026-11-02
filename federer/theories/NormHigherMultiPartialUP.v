(** Federer (1969), 3.1.11, p. 223: the multiindex
    derivatives defined from the kth differential on Euclidean space. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom RealNormUP GrassmannAbbreviations
  FiniteCoordinates SymmetricAlgebra SymmetricForms SymmetricFormExtension
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomials SymmetricMonomialTuples
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherSymmetricFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_multi_partial_arguments]: the coordinate
    vectors in the monomial e^alpha, Federer 3.1.11,
    p. 223. Their number is exactly the total degree k. *)
Definition norm_multi_partial_arguments (R : realType) n k (alpha : symmetric_indices n k) :
    {ffun 'I_k->R_n R n} :=
  [ffun i=>tnth (symmetric_monomial_tuple (@coordinate_basis R n) alpha) i].

(** Source for [has_norm_multi_partial]: D^alpha f(a) is
    the evaluation of the actual kth differential on e^alpha,
    as defined in Federer 3.1.11, p. 223. Existence of
    the full differential is retained in this graph. *)
Definition has_norm_multi_partial (R : realType) n (Y : lmodType R)
    (NX : R_n R n->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R n}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (A : R_n R n->Prop) (f : R_n R n->Y) k
    (alpha : symmetric_indices n k) a y :=
  exists z : Z k, has_norm_higher_differential NX ev ZN A f k a z /\
    @ev k (norm_multi_partial_arguments R alpha) z=y.

(** Source for [norm_multi_partial_unique]: the multiindex
    derivative has a unique value, Federer 3.1.11, p. 223,
    by uniqueness of the kth differential. *)
Lemma norm_multi_partial_unique (R : realType) n (Y : lmodType R)
    (NX : R_n R n->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R n}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : R_n R n->Prop) (f : R_n R n->Y) k (alpha : symmetric_indices n k) a y w :
  has_norm_multi_partial NX ev ZN A f alpha a y ->
  has_norm_multi_partial NX ev ZN A f alpha a w -> y=w.
Proof.
move=>[z [hz <-]] [q [hq <-]].
by rewrite (norm_higher_differential_unique hNX hNY hZ hz hq).
Qed.

(** Source for [norm_multi_partial_form_evaluation]: the
    multiindex derivative is precisely the pairing with e^alpha
    in the Chapter 1 symmetric algebra, Federer 3.1.11, p. 223. *)
Lemma norm_multi_partial_form_evaluation (R : realType) n (Y : lmodType R)
    (NX : R_n R n->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R n}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (A : R_n R n->Prop) (f : R_n R n->Y) k
    (alpha : symmetric_indices n k) a (phi : S_m (R_n R n) Y k) :
  is_norm_higher_differential_form NX ev ZN A f k a phi ->
  has_norm_multi_partial NX ev ZN A f alpha a
    (sform_homogeneous phi (symmetric_monomial (@coordinate_basis R n)
      (symmetric_indices_unbound alpha))).
Proof.
move=>[z [hz he]]; exists z; split; first exact hz.
rewrite he symmetric_monomial_form_value.
congr (phi _); apply: eq_from_tnth=>i.
by rewrite tnth_mktuple /norm_multi_partial_arguments ffunE.
Qed.
