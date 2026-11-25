(** Federer (1969), 1.9.3, p. 42: summation over Xi(k,m). Supporting
    first-coordinate reindexing for an induction from the binomial theorem.
    The sources use direct fibre counting; this local supporting
    decomposition gives the equivalent iterated sum. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds SymmetricIndexRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_index_code_onto]: Federer 1.9.3,
    p. 42, supporting fact that every summation index is represented
    by the previously proved first-coordinate decomposition. *)
Lemma symmetric_index_code_onto n m (a : symmetric_indices n m) :
  a \in codom (@symmetric_index_code_to_indices n m).
Proof.
apply/codomP; have [c hc] := symmetric_index_code_to_indices_surjective a.
exists c; exact: esym hc.
Qed.

(** Source for [symmetric_indices_to_code]: Federer 1.9.3,
    p. 42, supporting inverse of the finite index representation. *)
Definition symmetric_indices_to_code n m (a : symmetric_indices n m) : symmetric_index_code n m :=
  iinv (symmetric_index_code_onto a).

(** Source for [symmetric_indices_to_codeK]: Federer 1.9.3,
    p. 42, reconstruction after conversion recovers the summation index. *)
Lemma symmetric_indices_to_codeK n m :
  cancel (@symmetric_indices_to_code n m) (@symmetric_index_code_to_indices n m).
Proof. move=> a; exact: f_iinv. Qed.

(** Source for [symmetric_index_code_to_indicesK]: Federer
    1.9.3, p. 42, conversion after reconstruction recovers the code. *)
Lemma symmetric_index_code_to_indicesK n m :
  cancel (@symmetric_index_code_to_indices n m) (@symmetric_indices_to_code n m).
Proof.
move=> c; apply: (@symmetric_index_code_to_indices_injective n m).
exact: symmetric_indices_to_codeK.
Qed.

(** Source for [symmetric_index_code_bijective]: Federer 1.9.3,
    p. 42, the code representation is a bijection and can reindex sums. *)
Lemma symmetric_index_code_bijective n m : bijective (@symmetric_index_code_to_indices n m).
Proof.
exists (@symmetric_indices_to_code n m);
  [exact: symmetric_index_code_to_indicesK | exact: symmetric_indices_to_codeK].
Qed.

(** Source for [symmetric_indices_cons_degree]: Federer 1.9.3,
    p. 42, supporting fact: a first exponent i and a tail
    of degree m-i combine to an exponent tuple of degree m. *)
Lemma symmetric_indices_cons_degree n m (i : 'I_m.+1) (a : symmetric_indices n (m-i)%N) :
  symmetric_multi_degree (symmetric_multi_cons (val i) (symmetric_indices_unbound a)) = m.
Proof.
rewrite symmetric_multi_degree_cons symmetric_indices_unbound_degree addnC subnK //.
by move: (valP i); rewrite ltnS.
Qed.

Arguments symmetric_indices_cons_degree {n m} i a.

(** Source for [symmetric_indices_cons]: Federer 1.9.3,
    p. 42, supporting insertion of a first exponent into a
    tail index with the complementary total degree. *)
Definition symmetric_indices_cons n m (i : 'I_m.+1) (a : symmetric_indices n (m-i)%N) :
    symmetric_indices n.+1 m :=
  symmetric_indices_bound (Sub (symmetric_multi_cons (val i) (symmetric_indices_unbound a))
    (introT eqP (symmetric_indices_cons_degree i a))).

Arguments symmetric_indices_cons {n m} i a.

(** Source for [symmetric_indices_cons_unbound]: Federer 1.9.3,
    p. 42, forgetting redundant bounds after insertion recovers
    the first exponent followed by the original tail tuple. *)
Lemma symmetric_indices_cons_unbound n m (i : 'I_m.+1) (a : symmetric_indices n (m-i)%N) :
  symmetric_indices_unbound (symmetric_indices_cons i a) =
    symmetric_multi_cons (val i) (symmetric_indices_unbound a).
Proof.
have h := @symmetric_indices_boundK n.+1 m
  (Sub (symmetric_multi_cons (val i) (symmetric_indices_unbound a))
    (introT eqP (symmetric_indices_cons_degree i a))).
exact (congr1 (fun b : symmetric_degree_indices n.+1 m => val b) h).
Qed.

Arguments symmetric_indices_cons_unbound {n m} i a.

(** Source for [symmetric_index_code_unboundE]: Federer 1.9.3,
    p. 42, the tuple underlying a code's finite index equals
    the tuple reconstructed directly from that code. *)
Lemma symmetric_index_code_unboundE n m (c : symmetric_index_code n m) :
  symmetric_indices_unbound (symmetric_index_code_to_indices c) = symmetric_index_decode n m c.
Proof.
have h := @symmetric_indices_boundK n m
  (Sub (symmetric_index_decode n m c) (introT eqP (symmetric_index_decode_degree c))).
exact (congr1 (fun b : symmetric_degree_indices n m => val b) h).
Qed.

(** Source for [symmetric_index_code_consE]: Federer 1.9.3,
    p. 42, the finite bijection respects the first-coordinate decomposition. *)
Lemma symmetric_index_code_consE n m (i : 'I_m.+1) (t : symmetric_index_code n (m-i)%N) :
  @symmetric_index_code_to_indices n.+1 m (existT _ i t) =
    symmetric_indices_cons i (symmetric_index_code_to_indices t).
Proof.
apply: (can_inj (@symmetric_indices_forgetK n.+1 m)).
rewrite /symmetric_index_code_to_indices /symmetric_indices_cons !symmetric_indices_boundK.
apply: val_inj; change (symmetric_multi_cons (val i) (symmetric_index_decode n (m-i)%N t) =
  symmetric_multi_cons (val i) (symmetric_indices_unbound (symmetric_index_code_to_indices t))).
by rewrite symmetric_index_code_unboundE.
Qed.

(** Source for [symmetric_indices_sum_cons]: Federer 1.9.3,
    p. 42, supporting reindexing of the multinomial sum by
    the first exponent and the remaining exponent tuple. *)
Lemma symmetric_indices_sum_cons (Z : zmodType) n m (F : symmetric_indices n.+1 m -> Z) :
  (\sum_a F a = \sum_(i < m.+1) \sum_(a : symmetric_indices n (m-i)%N)
    F (symmetric_indices_cons i a))%R.
Proof.
rewrite (reindex (@symmetric_index_code_to_indices n.+1 m)
  (onW_bij _ (symmetric_index_code_bijective n.+1 m))).
transitivity (\sum_(i < m.+1) \sum_(t : symmetric_index_code n (m-i)%N)
  F (@symmetric_index_code_to_indices n.+1 m (existT _ i t)))%R.
- rewrite sig_big_dep /=.
  apply: eq_bigr=> [[i t]] _; by [].
- apply: eq_bigr=> i _.
  rewrite (reindex (@symmetric_index_code_to_indices n (m-i)%N)
    (onW_bij _ (symmetric_index_code_bijective n (m-i)%N))).
  apply: eq_bigr=> t _; by rewrite symmetric_index_code_consE.
Qed.
