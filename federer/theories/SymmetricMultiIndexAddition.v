(** Federer (1969), 1.10.2, p. 45: exponents add when multiplying the dual
    monomials. Supporting nonnegative multiindex arithmetic. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricExponentBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_multi_add]: Federer 1.10.2, p. 45,
    supporting coordinatewise addition of nonnegative exponents. *)
Definition symmetric_multi_add n (a b : symmetric_multi_index n) : symmetric_multi_index n :=
  [ffun i => a i + b i].

(** Source for [symmetric_multi_addE]: Federer 1.10.2, p. 45,
    evaluate the sum at a coordinate. *)
Lemma symmetric_multi_addE n (a b : symmetric_multi_index n) i :
  symmetric_multi_add a b i = a i + b i.
Proof. by rewrite /symmetric_multi_add ffunE. Qed.

(** Source for [symmetric_multi_addC]: Federer 1.10.2, p. 45,
    supporting commutativity of exponent addition. *)
Lemma symmetric_multi_addC n : commutative (@symmetric_multi_add n).
Proof. move=> a b; apply/ffunP=> i; by rewrite !symmetric_multi_addE addnC. Qed.

(** Source for [symmetric_multi_addA]: Federer 1.10.2, p. 45,
    supporting associativity of exponent addition. *)
Lemma symmetric_multi_addA n : associative (@symmetric_multi_add n).
Proof. move=> a b c; apply/ffunP=> i; by rewrite !symmetric_multi_addE addnA. Qed.

(** Source for [symmetric_multi_add0]: Federer 1.10.2, p. 45,
    the zero exponent is neutral for addition. *)
Lemma symmetric_multi_add0 n (a : symmetric_multi_index n) :
  symmetric_multi_add a (symmetric_multi_zero n) = a.
Proof. apply/ffunP=> i; by rewrite symmetric_multi_addE /symmetric_multi_zero ffunE addn0. Qed.

(** Source for [symmetric_multi_degree_add]: Federer 1.10.2,
    p. 45, total degrees add with the exponent tuples. *)
Lemma symmetric_multi_degree_add n (a b : symmetric_multi_index n) :
  symmetric_multi_degree (symmetric_multi_add a b) =
    symmetric_multi_degree a + symmetric_multi_degree b.
Proof.
rewrite /symmetric_multi_degree -big_split.
apply: eq_bigr=> i _; exact: symmetric_multi_addE.
Qed.

(** Source for [symmetric_multi_difference_addl]: Federer
    1.10.2, p. 45, supporting cancellation: (alpha+beta)-alpha=beta. *)
Lemma symmetric_multi_difference_addl n (a b : symmetric_multi_index n) :
  symmetric_multi_difference (symmetric_multi_add a b) a = b.
Proof.
apply/ffunP=> i; by rewrite /symmetric_multi_difference ffunE symmetric_multi_addE addKn.
Qed.

(** Source for [symmetric_multi_add_difference]: Federer
    1.10.2, p. 45, under beta<=alpha the tuples beta and alpha-beta
    sum to alpha; used to identify the unique diagonal summand. *)
Lemma symmetric_multi_add_difference n (a b : symmetric_multi_index n) :
  (forall i, b i <= a i) -> symmetric_multi_add b (symmetric_multi_difference a b) = a.
Proof.
move=> hab; apply/ffunP=> i.
by rewrite symmetric_multi_addE /symmetric_multi_difference ffunE addnC subnK.
Qed.

(** Source for [symmetric_multi_add_bound]: Federer 1.10.2,
    p. 45, each summand is coordinatewise bounded by the exponent sum. *)
Lemma symmetric_multi_add_bound n (a b : symmetric_multi_index n) i :
  a i <= symmetric_multi_add a b i.
Proof. by rewrite symmetric_multi_addE leq_addr. Qed.
