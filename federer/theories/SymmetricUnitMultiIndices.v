(** Federer (1969), 1.10.2, p. 45: individual basis vectors and the empty
    product within the monomial notation. Supporting boundary identities for
    identifying the actual dual one-form products. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricAlgebra SymmetricMultiIndices SymmetricIndexBounds
  SymmetricMonomials SymmetricDividedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_multi_unit]: Federer 1.10.2, p. 45,
    the exponent tuple having one in position i and zero elsewhere. *)
Definition symmetric_multi_unit n (i : 'I_n) : symmetric_multi_index n :=
  [ffun j => if j == i then 1%N else 0%N].

(** Source for [symmetric_multi_unit_degree]: Federer 1.10.2,
    p. 45, this exponent tuple has total degree one. *)
Lemma symmetric_multi_unit_degree n (i : 'I_n) :
  symmetric_multi_degree (symmetric_multi_unit i) = 1%N.
Proof.
rewrite /symmetric_multi_degree /symmetric_multi_unit.
under eq_bigr do rewrite ffunE.
rewrite (bigD1 i) //= eqxx.
have hz : (\sum_(j < n | j != i) (if j == i then 1 else 0))%N = 0%N.
  apply: big1=> j hj; by rewrite (negbTE hj).
by rewrite hz addn0.
Qed.

(** Source for [symmetric_multi_unit_injective]: Federer 1.10.2,
    p. 45, distinct coordinate positions have distinct unit exponent tuples. *)
Lemma symmetric_multi_unit_injective n : injective (@symmetric_multi_unit n).
Proof.
move=> i j h.
have hh := congr1 (fun a : symmetric_multi_index n => a i) h.
rewrite /symmetric_multi_unit !ffunE eqxx in hh.
case: ifP hh=> [/eqP ->|_]; by [].
Qed.

(** Source for [symmetric_multi_unit_factorial]: Federer 1.10.2,
    p. 45, the factorial of a unit exponent tuple is one. *)
Lemma symmetric_multi_unit_factorial n (i : 'I_n) :
  symmetric_multi_factorial (symmetric_multi_unit i) = 1%N.
Proof.
apply: big1=> j _; rewrite /symmetric_multi_unit ffunE.
by case: ifP.
Qed.

(** Source for [symmetric_multi_zero_factorial]: Federer 1.10.2,
    p. 45, the factorial of the zero tuple is one, including no coordinates. *)
Lemma symmetric_multi_zero_factorial n :
  symmetric_multi_factorial (symmetric_multi_zero n) = 1%N.
Proof. apply: big1=> j _; by rewrite /symmetric_multi_zero ffunE. Qed.

(** Source for [symmetric_monomial_word_zero]: Federer 1.10.2,
    p. 45, the zero exponent gives the empty monomial word. *)
Lemma symmetric_monomial_word_zero (T : Type) n (v : 'I_n -> T) :
  symmetric_monomial_word v (symmetric_multi_zero n) = [::].
Proof.
rewrite /symmetric_monomial_word.
elim: (enum 'I_n)=> [|i s ih] //=.
by rewrite /symmetric_multi_zero ffunE /= ih.
Qed.

(** Source for [symmetric_monomial_word_unit]: Federer 1.10.2,
    p. 45, the unit exponent tuple gives the one-letter word v_i. *)
Lemma symmetric_monomial_word_unit (T : eqType) n (v : 'I_n -> T) (i : 'I_n) :
  symmetric_monomial_word v (symmetric_multi_unit i) = [:: v i].
Proof.
have hs : size (symmetric_monomial_word v (symmetric_multi_unit i)) = 1%N.
  by rewrite symmetric_monomial_word_size symmetric_multi_unit_degree.
have hm : v i \in symmetric_monomial_word v (symmetric_multi_unit i).
  apply/flattenP; exists (nseq (symmetric_multi_unit i i) (v i)).
  - apply/mapP; exists i; first exact: mem_enum; by [].
  - by rewrite /symmetric_multi_unit ffunE eqxx /= inE eqxx.
move: hs hm; case: (symmetric_monomial_word v (symmetric_multi_unit i))=> [|x s] //=.
case: s=> [|y s] //= _; rewrite inE=> /eqP <-; by [].
Qed.

(** Source for [symmetric_monomial_unit]: Federer 1.10.2,
    p. 45, a unit exponent monomial is its generating vector. *)
Lemma symmetric_monomial_unit (K : fieldType) (V : lmodType K)
    n (v : 'I_n -> V) i :
  symmetric_monomial v (symmetric_multi_unit i) = symmetric_generator (v i).
Proof.
by rewrite /symmetric_monomial symmetric_monomial_word_unit
  symmetric_word_cons symmetric_word_nil symmetric_product_unitr.
Qed.

(** Source for [symmetric_divided_monomial_zero]: Federer 1.10.2,
    p. 45, the divided zero monomial is the scalar unit. *)
Lemma symmetric_divided_monomial_zero (K : fieldType) (V : lmodType K)
    n (v : 'I_n -> V) :
  symmetric_divided_monomial v (symmetric_multi_zero n) = symmetric_unit V.
Proof.
by rewrite /symmetric_divided_monomial symmetric_multi_zero_factorial invr1 scale1r
  /symmetric_monomial symmetric_monomial_word_zero symmetric_word_nil.
Qed.

(** Source for [symmetric_unit_index]: Federer 1.10.2, p. 45,
    the unit exponent regarded as a finite member of Xi(n,1). *)
Definition symmetric_unit_index n (i : 'I_n) : symmetric_indices n 1 :=
  symmetric_indices_bound (Sub (symmetric_multi_unit i) (introT eqP (symmetric_multi_unit_degree i))).

(** Source for [symmetric_unit_indexE]: Federer 1.10.2, p. 45,
    forgetting its redundant bounds recovers the unit exponent. *)
Lemma symmetric_unit_indexE n (i : 'I_n) :
  symmetric_indices_unbound (symmetric_unit_index i) = symmetric_multi_unit i.
Proof.
have h := @symmetric_indices_boundK n 1
  (Sub (symmetric_multi_unit i) (introT eqP (symmetric_multi_unit_degree i))).
exact: (congr1 (fun z : symmetric_degree_indices n 1 => val z) h).
Qed.
