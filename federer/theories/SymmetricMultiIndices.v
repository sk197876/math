(** Federer (1969), 1.9.2, p. 42: nonnegative integer multiindices and the
    set Xi(n,m) of those whose sum is m. Supporting head/tail decomposition
    follows the induction on dimension. *)
From mathcomp Require Import all_boot all_order ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_multi_index]: Federer 1.9.2, p. 42,
    n-term sequences of nonnegative integers. Finite functions record
    the n entries without imposing any bound on their values. *)
Definition symmetric_multi_index n := {ffun 'I_n -> nat}.

(** Source for [symmetric_multi_degree]: Federer 1.9.2, p. 42,
    the displayed sum of the entries of a multiindex. *)
Definition symmetric_multi_degree n (a : symmetric_multi_index n) :=
  (\sum_(i < n) a i)%N.

(** Source for [symmetric_multi_zero]: Federer 1.9.2, p. 42,
    supporting zero multiindex, which indexes the empty monomial. *)
Definition symmetric_multi_zero n : symmetric_multi_index n := [ffun _ => 0].

(** Source for [symmetric_multi_degree_zero]: Federer 1.9.2,
    p. 42, the zero multiindex has total degree zero. *)
Lemma symmetric_multi_degree_zero n : symmetric_multi_degree (symmetric_multi_zero n) = 0.
Proof. by rewrite /symmetric_multi_degree; apply: big1 => i _; rewrite ffunE. Qed.

(** Source for [symmetric_multi_entry_bound]: Federer 1.9.2,
    p. 42, supporting finiteness of Xi(n,m): every nonnegative entry
    is bounded by the sum of all entries. *)
Lemma symmetric_multi_entry_bound n (a : symmetric_multi_index n) i :
  a i <= symmetric_multi_degree a.
Proof. by rewrite /symmetric_multi_degree (bigD1 i) //= leq_addr. Qed.

(** Source for [symmetric_multi_head]: Federer 1.9.2, p. 42, supporting
    first-coordinate projection for the dimension induction. *)
Definition symmetric_multi_head n (a : symmetric_multi_index n.+1) := a ord0.

(** Source for [symmetric_multi_tail]: Federer 1.9.2, p. 42,
    supporting deletion of the first coordinate in the same induction. *)
Definition symmetric_multi_tail n (a : symmetric_multi_index n.+1) :
    symmetric_multi_index n := [ffun i => a (lift ord0 i)].

(** Source for [symmetric_multi_cons]: Federer 1.9.2, p. 42,
    supporting insertion of a first coordinate before an n-term multiindex. *)
Definition symmetric_multi_cons n k (a : symmetric_multi_index n) :
    symmetric_multi_index n.+1 :=
  [ffun i => if unlift ord0 i is Some j then a j else k].

(** Source for [symmetric_multi_cons_head]: Federer 1.9.2,
    p. 42, supporting cancellation: head recovers the inserted first entry. *)
Lemma symmetric_multi_cons_head n k (a : symmetric_multi_index n) :
  symmetric_multi_head (symmetric_multi_cons k a) = k.
Proof. by rewrite /symmetric_multi_head /symmetric_multi_cons ffunE unlift_none. Qed.

(** Source for [symmetric_multi_cons_tail]: Federer 1.9.2,
    p. 42, supporting cancellation: tail recovers the original multiindex. *)
Lemma symmetric_multi_cons_tail n k (a : symmetric_multi_index n) :
  symmetric_multi_tail (symmetric_multi_cons k a) = a.
Proof. by apply/ffunP=> i; rewrite /symmetric_multi_tail /symmetric_multi_cons !ffunE liftK. Qed.

(** Source for [symmetric_multi_head_tail]: Federer 1.9.2,
    p. 42, supporting reconstruction from the head and tail coordinates. *)
Lemma symmetric_multi_head_tail n (a : symmetric_multi_index n.+1) :
  symmetric_multi_cons (symmetric_multi_head a) (symmetric_multi_tail a) = a.
Proof.
apply/ffunP=> i; rewrite /symmetric_multi_cons ffunE.
case: (unliftP ord0 i) => [j ->|->] => //.
by rewrite /symmetric_multi_tail ffunE.
Qed.

(** Source for [symmetric_multi_degree_cons]: Federer 1.9.2,
    p. 42, supporting degree calculation in the dimension induction:
    the total degree is the first entry plus the tail's total degree. *)
Lemma symmetric_multi_degree_cons n k (a : symmetric_multi_index n) :
  symmetric_multi_degree (symmetric_multi_cons k a) = k + symmetric_multi_degree a.
Proof.
rewrite /symmetric_multi_degree big_ord_recl
  /symmetric_multi_cons ffunE unlift_none.
congr (_ + _); apply: eq_bigr => i _; by rewrite ffunE liftK.
Qed.

(** Source for [symmetric_multi_index_empty]: Federer 1.9.2,
    p. 42, supporting boundary: there is exactly one zero-term multiindex. *)
Lemma symmetric_multi_index_empty (a : symmetric_multi_index 0) :
  a = symmetric_multi_zero 0.
Proof. apply/ffunP=> i; by case: i => i. Qed.

(** Source for [symmetric_indices]: Federer 1.9.2, p. 42,
    the set Xi(n,m). Entries are bounded by m to give a finite type;
    the entry-bound lemma justifies this representation. *)
Definition symmetric_indices n m :=
  {a : {ffun 'I_n -> 'I_m.+1} | (\sum_(i < n) val (a i))%N == m}.
