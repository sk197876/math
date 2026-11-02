(** Federer (1969), 1.9.2, p. 42: Xi(n,m), the set of nonnegative n-tuples
    summing to m, indexes the degree-m monomial basis. The supporting
    bijections below justify the finite representation of this index set. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_degree_indices]: Federer 1.9.2,
    p. 42, the predicate defining Xi(n,m), before imposing the
    redundant bound by m on every coordinate. *)
Definition symmetric_degree_indices n m :=
  {a : symmetric_multi_index n | symmetric_multi_degree a == m}.

(** Source for [symmetric_indices_unbound]: Federer 1.9.2,
    p. 42, supporting map forgetting the coordinate bounds. *)
Definition symmetric_indices_unbound n m (a : symmetric_indices n m) :
    symmetric_multi_index n := [ffun i => val (val a i)].

(** Source for [symmetric_indices_unbound_degree]: Federer
    1.9.2, p. 42, forgetting the bounds preserves total degree. *)
Lemma symmetric_indices_unbound_degree n m (a : symmetric_indices n m) :
  symmetric_multi_degree (symmetric_indices_unbound a) = m.
Proof.
rewrite /symmetric_multi_degree /symmetric_indices_unbound.
under eq_bigr do rewrite ffunE.
exact: eqP (valP a).
Qed.

(** Source for [symmetric_indices_forget]: Federer 1.9.2,
    p. 42, supporting inclusion of the finite model of Xi(n,m)
    into its unbounded predicate model. *)
Definition symmetric_indices_forget n m (a : symmetric_indices n m) :
    symmetric_degree_indices n m :=
  Sub (symmetric_indices_unbound a) (introT eqP (symmetric_indices_unbound_degree a)).

(** Source for [symmetric_degree_index_bound]: Federer 1.9.2,
    p. 42, each entry of a nonnegative tuple of sum m is at most m. *)
Lemma symmetric_degree_index_bound n m (a : symmetric_degree_indices n m) i :
  val a i < m.+1.
Proof.
rewrite ltnS.
have h := symmetric_multi_entry_bound (val a) i.
by rewrite (eqP (valP a)) in h.
Qed.

(** Source for [symmetric_indices_bound_function]: Federer
    1.9.2, p. 42, supporting insertion of the redundant upper
    bound into each coordinate of a degree-m multiindex. *)
Definition symmetric_indices_bound_function n m (a : symmetric_degree_indices n m) :
    {ffun 'I_n -> 'I_m.+1} :=
  [ffun i => Ordinal (symmetric_degree_index_bound a i)].

(** Source for [symmetric_indices_bound_degree]: Federer 1.9.2,
    p. 42, insertion of the coordinate bounds preserves the sum. *)
Lemma symmetric_indices_bound_degree n m (a : symmetric_degree_indices n m) :
  (\sum_(i < n) val (symmetric_indices_bound_function a i))%N = m.
Proof.
rewrite /symmetric_indices_bound_function.
under eq_bigr do rewrite ffunE /=.
exact: eqP (valP a).
Qed.

(** Source for [symmetric_indices_bound]: Federer 1.9.2,
    p. 42, supporting map from the unbounded predicate model of
    Xi(n,m) to its finite bounded model. *)
Definition symmetric_indices_bound n m (a : symmetric_degree_indices n m) :
    symmetric_indices n m :=
  Sub (symmetric_indices_bound_function a) (introT eqP (symmetric_indices_bound_degree a)).

(** Source for [symmetric_indices_forgetK]: Federer 1.9.2,
    p. 42, supporting cancellation: forgetting and reinserting the
    bounds recovers the same finite multiindex. *)
Lemma symmetric_indices_forgetK n m :
  cancel (@symmetric_indices_forget n m) (@symmetric_indices_bound n m).
Proof.
move=> a; apply: val_inj; apply/ffunP=> i.
rewrite /symmetric_indices_bound /symmetric_indices_bound_function
  /symmetric_indices_forget /symmetric_indices_unbound /= !ffunE.
apply: val_inj; by rewrite /= ffunE.
Qed.

(** Source for [symmetric_indices_boundK]: Federer 1.9.2,
    p. 42, supporting cancellation: inserting and forgetting bounds
    recovers the original nonnegative tuple. *)
Lemma symmetric_indices_boundK n m :
  cancel (@symmetric_indices_bound n m) (@symmetric_indices_forget n m).
Proof. move=> a; apply: val_inj; apply/ffunP=> i; by rewrite /symmetric_indices_bound /symmetric_indices_bound_function
  /symmetric_indices_forget /symmetric_indices_unbound /= !ffunE. Qed.
