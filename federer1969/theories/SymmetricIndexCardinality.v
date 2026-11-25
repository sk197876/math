(** Federer (1969), 1.9.2, p. 42: card Xi(n,m) equals binomial(m+n-1,n-1)
    when n is positive. The proof below uses first-coordinate recursion and
    Pascal's identity instead of the sources' separator bijection. Zero
    variables are treated separately. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds SymmetricIndexRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_index_code_card_zero]: Federer
    1.9.2, p. 42, supporting boundary: an empty tuple has
    sum zero, so Xi(0,m) has one element precisely when m=0. *)
Lemma symmetric_index_code_card_zero m :
  #|symmetric_index_code 0 m| = (m == 0).
Proof.
rewrite /symmetric_index_code card_sig.
case: (m == 0); first exact: card_unit.
exact: card0.
Qed.

(** Source for [symmetric_index_code_card_successor]: Federer
    1.9.2, p. 42, supporting recurrence: partition the tuples
    according to their first coordinate i between zero and m. *)
Lemma symmetric_index_code_card_successor n m :
  #|symmetric_index_code n.+1 m| =
    \sum_(i < m.+1) #|symmetric_index_code n (m-i)|.
Proof.
rewrite /symmetric_index_code -/symmetric_index_code card_tagged sumnE big_map.
exact: big_enum.
Qed.

(** Source for [symmetric_index_code_card_line]: Federer
    1.9.2, p. 42, there is exactly one one-term tuple of sum m. *)
Lemma symmetric_index_code_card_line m : #|symmetric_index_code 1 m| = 1.
Proof.
rewrite symmetric_index_code_card_successor.
under eq_bigr do rewrite symmetric_index_code_card_zero.
rewrite (bigD1 ord_max) //= subnn eqxx.
have hz : (\sum_(i < m.+1 | i != ord_max) (m-i == 0)) = 0.
  apply: big1=> i hi.
  have him : (i <= m)%N by move: (valP i); rewrite ltnS.
  have hne : (i : nat) != m.
    by rewrite -[m]/(val (ord_max : 'I_m.+1)) (inj_eq val_inj).
  by rewrite subn_eq0 leq_eqVlt eq_sym (negbTE hne) (ltnNge m i) him.
by rewrite hz addn0.
Qed.

(** Source for [symmetric_binomial_sum]: Federer 1.9.2,
    p. 42, supporting sum identity used to solve the counting
    recurrence, proved by Pascal's identity. *)
Lemma symmetric_binomial_sum n m :
  \sum_(i < m.+1) 'C(i+n,n) = 'C((m+n).+1,n.+1).
Proof.
elim: m=> [|m ih].
- by rewrite big_ord1 add0n !binn.
- by rewrite big_ord_recr /= ih -binS.
Qed.

(** Source for [symmetric_binomial_reverse_sum]: Federer
    1.9.2, p. 42, the same supporting sum with reversed first
    coordinate, as required by the tail degree m-i. *)
Lemma symmetric_binomial_reverse_sum n m :
  \sum_(i < m.+1) 'C(m-i+n,n) = 'C((m+n).+1,n.+1).
Proof.
rewrite (reindex_inj rev_ord_inj).
have he : (\sum_(i < m.+1) 'C(m-rev_ord i+n,n)) =
    \sum_(i < m.+1) 'C(i+n,n).
  apply: eq_bigr=> i _; rewrite /= subKn //.
  by move: (valP i); rewrite ltnS.
by rewrite he symmetric_binomial_sum.
Qed.

(** Source for [symmetric_index_code_card_positive]: Federer
    1.9.2, p. 42, supporting evaluation of the recursively
    represented index count in positive dimension. *)
Lemma symmetric_index_code_card_positive n m :
  #|symmetric_index_code n.+1 m| = 'C(m+n,n).
Proof.
elim: n m => [m|n ih m].
- by rewrite symmetric_index_code_card_line bin0.
- rewrite symmetric_index_code_card_successor.
  under eq_bigr do rewrite ih.
  by rewrite symmetric_binomial_reverse_sum addnS.
Qed.

(** Source for [card_symmetric_indices]: Federer 1.9.2,
    p. 42, the displayed formula card Xi(n,m)=binomial(m+n-1,n-1),
    with its necessary positive-dimension hypothesis expressed as n+1. *)
Theorem card_symmetric_indices n m :
  #|{: symmetric_indices n.+1 m}| = 'C(m+n,n).
Proof. by rewrite -symmetric_index_code_cardinality symmetric_index_code_card_positive. Qed.

(** Source for [card_symmetric_indices_zero]: Federer 1.9.2, p. 42, explicit
    zero-dimensional boundary for the index set, discussed. *)
Theorem card_symmetric_indices_zero m :
  #|{: symmetric_indices 0 m}| = (m == 0).
Proof. by rewrite -symmetric_index_code_cardinality symmetric_index_code_card_zero. Qed.
