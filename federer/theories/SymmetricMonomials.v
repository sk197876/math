(** Federer (1969), 1.9.2, p. 42: e^alpha is the symmetric product of
    alpha_i copies of each e_i. These definitions and supporting identities
    allow arbitrary vectors and fields, without a basis hypothesis. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP AlgebraUP GradedAlgebra SymmetricAlgebra
  SymmetricGrading SymmetricMaps SymmetricMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_monomial_word]: Federer 1.9.2,
    p. 42, the ordered list underlying e^alpha: repeat e_i
    alpha_i times, in increasing order of i. *)
Definition symmetric_monomial_word (T : Type) n (e : 'I_n -> T)
    (a : symmetric_multi_index n) : seq T :=
  flatten [seq nseq (a i) (e i) | i <- enum 'I_n].

(** Source for [symmetric_monomial_word_size]: Federer 1.9.2,
    p. 42, the total number of factors of e^alpha is the sum
    of the entries of alpha. *)
Lemma symmetric_monomial_word_size (T : Type) n (e : 'I_n -> T)
    (a : symmetric_multi_index n) :
  size (symmetric_monomial_word e a) = symmetric_multi_degree a.
Proof.
rewrite /symmetric_monomial_word /symmetric_multi_degree -big_enum.
elim: (enum 'I_n) => [|i s ih] /=; first by rewrite big_nil.
by rewrite size_cat size_nseq big_cons ih.
Qed.

(** Source for [symmetric_monomial_word_map]: Federer 1.9.2,
    p. 42, supporting functoriality: applying a function to each
    repeated factor applies that function to the original family. *)
Lemma symmetric_monomial_word_map (T U : Type) n (e : 'I_n -> T)
    (a : symmetric_multi_index n) (f : T -> U) :
  map f (symmetric_monomial_word e a) = symmetric_monomial_word (f \o e) a.
Proof.
rewrite /symmetric_monomial_word map_flatten -map_comp.
congr 1 (flatten _); apply: eq_map => i; exact: map_nseq.
Qed.

Section Monomials.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.

(** Source for [symmetric_monomial]: Federer 1.9.2, p. 42,
    the displayed product e^alpha of powers of the family e. *)
Definition symmetric_monomial (a : symmetric_multi_index n) : symmetric_space V :=
  symmetric_word (symmetric_monomial_word e a).

(** Source for [symmetric_monomial_homogeneous]: Federer 1.9.2,
    p. 42, e^alpha belongs to the symmetric power whose degree
    is the sum of the entries of alpha. *)
Lemma symmetric_monomial_homogeneous a :
  homogeneous (symmetric_grading V) (symmetric_multi_degree a) (symmetric_monomial a).
Proof.
rewrite /symmetric_monomial -(symmetric_monomial_word_size e a).
exact: symmetric_word_homogeneous.
Qed.
End Monomials.

(** Source for [symmetric_monomial_natural]: Federer 1.9.2,
    p. 42, supporting transport of the monomial basis: the induced
    algebra map sends e^alpha to (f(e))^alpha. *)
Lemma symmetric_monomial_natural (K : fieldType) (V W : lmodType K)
    n (e : 'I_n -> V) (a : symmetric_multi_index n) (f : {linear V -> W}) :
  symmetric_algebra_map f (symmetric_monomial e a) = symmetric_monomial (f \o e) a.
Proof. by rewrite /symmetric_monomial symmetric_algebra_map_word symmetric_monomial_word_map. Qed.
