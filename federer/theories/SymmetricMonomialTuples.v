(** Federer (1969), 1.10.5, p. 48: supporting evaluation of monomials and
    the final weighted polynomial estimate. A monomial is evaluated on its
    explicit list of repeated factors. The tuple construction is only
    bookkeeping for that already defined product. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded GradedComponents Hom HomogeneousHom
  SymmetricAlgebra SymmetricGrading SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomials SymmetricForms SymmetricFormWords SymmetricFormExtension
  SymmetricFormIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_monomial_word_member]: Federer 1.10.5,
    p. 48, supporting observation: every factor of a monomial
    is one of the specified vectors. This does not require the
    family to be independent or spanning. *)
Lemma symmetric_monomial_word_member (T : eqType) n (e : 'I_n -> T)
    (a : symmetric_multi_index n) x :
  x \in symmetric_monomial_word e a -> exists i, x=e i.
Proof.
rewrite /symmetric_monomial_word=> /flattenP [s /mapP [i hi ->] hx].
move: hx; rewrite mem_nseq=> /andP [_ /eqP hx]; by exists i.
Qed.

(** Source for [symmetric_monomial_tuple_size]: Federer 1.10.5,
    p. 48, supporting typing of the repeated-factor list:
    a degree-m monomial has exactly m factors. *)
Lemma symmetric_monomial_tuple_size (T : Type) n (e : 'I_n -> T) m
    (a : symmetric_indices n m) :
  size (symmetric_monomial_word e (symmetric_indices_unbound a)) == m.
Proof. by rewrite symmetric_monomial_word_size symmetric_indices_unbound_degree. Qed.

(** Source for [symmetric_monomial_tuple]: Federer 1.10.5,
    p. 48, the tuple of repeated factors of v^alpha, whose
    length is the degree of alpha. *)
Definition symmetric_monomial_tuple (T : Type) n (e : 'I_n -> T) m
    (a : symmetric_indices n m) : m.-tuple T :=
  @Tuple m T (symmetric_monomial_word e (symmetric_indices_unbound a))
    (symmetric_monomial_tuple_size e a).

(** Source for [symmetric_monomial_tuple_component]: Federer
    1.10.5, p. 48, supporting compatibility: the tuple's
    symmetric product is exactly the algebraic monomial. *)
Lemma symmetric_monomial_tuple_component (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) m (a : symmetric_indices n m) :
  component_val (symmetric_tuple_component (symmetric_monomial_tuple e a)) =
    symmetric_monomial e (symmetric_indices_unbound a).
Proof. by rewrite symmetric_tuple_componentE. Qed.

(** Source for [symmetric_monomial_form_value]: Federer 1.10.5,
    p. 48, supporting monomial evaluation: the homogeneous
    extension evaluates v^alpha by applying the form to the repeated
    factor tuple. *)
Lemma symmetric_monomial_form_value (K : fieldType) (V W : lmodType K)
    n (e : 'I_n -> V) m (a : symmetric_indices n m) (f : S_m V W m) :
  sform_homogeneous f (symmetric_monomial e (symmetric_indices_unbound a)) =
    f (symmetric_monomial_tuple e a).
Proof.
rewrite sform_homogeneousE /symmetric_monomial sform_extensionE.
exact (@sform_wordsE K V W m f (symmetric_monomial_tuple e a)).
Qed.
