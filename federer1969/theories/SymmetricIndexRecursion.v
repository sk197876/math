(** Federer (1969), 1.9.2, p. 42: the finite set Xi(n,m). Supporting
    first-coordinate decomposition for counting and summation. The sources
    count by separators; the recursive model here groups tuples by their
    first entry and is proved equivalent. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_index_code]: Federer 1.9.2, p. 42,
    supporting finite recursive representation of Xi(n,m): choose
    the first entry k between zero and m, then a tail of sum m-k.
    In zero variables the empty tuple exists exactly in degree zero. *)
Fixpoint symmetric_index_code n m : finType :=
  match n with
  | 0 => Finite.clone {u : unit | m == 0} _
  | k.+1 => Finite.clone {i : 'I_m.+1 & symmetric_index_code k (m-i)} _
  end.

(** Source for [symmetric_index_decode]: Federer 1.9.2,
    p. 42, supporting map reconstructing the tuple from its
    recursive first-entry and tail representation. *)
Fixpoint symmetric_index_decode n m : symmetric_index_code n m -> symmetric_multi_index n :=
  match n as k return symmetric_index_code k m -> symmetric_multi_index k with
  | 0 => fun _ => symmetric_multi_zero 0
  | k.+1 => fun c =>
      match c with existT i t => symmetric_multi_cons (val i) (@symmetric_index_decode k (m-i) t) end
  end.
Arguments symmetric_index_decode n m c : clear implicits.

(** Source for [symmetric_index_decode_degree]: Federer 1.9.2,
    p. 42, the recursive representation reconstructs a tuple
    whose entries sum to its specified degree m. *)
Lemma symmetric_index_decode_degree n m (c : symmetric_index_code n m) :
  symmetric_multi_degree (symmetric_index_decode n m c) = m.
Proof.
elim: n m c => [m c|n ih m [i t]] /=.
- rewrite symmetric_multi_degree_zero; exact: esym (eqP (valP c)).
- rewrite symmetric_multi_degree_cons ih addnC subnK //.
  by move: (valP i); rewrite ltnS.
Qed.

(** Source for [symmetric_index_decode_injective]: Federer
    1.9.2, p. 42, the first-coordinate representation is unique. *)
Lemma symmetric_index_decode_injective n m : injective (symmetric_index_decode n m).
Proof.
elim: n m => [m x y _|n ih m [i t] [j u] h].
- apply: val_inj; by case: (val x); case: (val y).
- have hij : i = j.
    apply: val_inj; have hh := congr1 (@symmetric_multi_head n) h.
    by rewrite !symmetric_multi_cons_head in hh.
  case: j / hij u h => u h.
  congr (existT _ i _); apply: ih.
  have ht := congr1 (@symmetric_multi_tail n) h.
  by rewrite !symmetric_multi_cons_tail in ht.
Qed.

(** Source for [symmetric_index_decode_surjective]: Federer
    1.9.2, p. 42, every nonnegative tuple of sum m admits
    a first-coordinate representation. *)
Lemma symmetric_index_decode_surjective n m (a : symmetric_multi_index n) :
  symmetric_multi_degree a = m ->
  exists c : symmetric_index_code n m, symmetric_index_decode n m c = a.
Proof.
elim: n m a => [m a hm|n ih m a hm].
- have hm0 : m == 0.
    by rewrite -hm (symmetric_multi_index_empty a) symmetric_multi_degree_zero.
  exists (Sub tt hm0); exact: esym (symmetric_multi_index_empty a).
- have hi : symmetric_multi_head a < m.+1.
    rewrite ltnS -hm; exact: symmetric_multi_entry_bound.
  pose i := Ordinal hi.
  have ht : symmetric_multi_degree (symmetric_multi_tail a) = m - i.
    have hs := symmetric_multi_degree_cons (symmetric_multi_head a) (symmetric_multi_tail a).
    rewrite symmetric_multi_head_tail hm in hs.
    change (symmetric_multi_degree (symmetric_multi_tail a) = m - symmetric_multi_head a).
    by rewrite hs addKn.
  have [t he] := ih _ _ ht.
  exists (existT _ i t); rewrite /= he; exact: symmetric_multi_head_tail.
Qed.

(** Source for [symmetric_index_code_to_indices]: Federer
    1.9.2, p. 42, supporting bijection from the recursive
    representation to the finite bounded set Xi(n,m). *)
Definition symmetric_index_code_to_indices n m (c : symmetric_index_code n m) :
    symmetric_indices n m :=
  symmetric_indices_bound (Sub (symmetric_index_decode n m c)
    (introT eqP (symmetric_index_decode_degree c))).

(** Source for [symmetric_index_code_to_indices_injective]:
    Federer 1.9.2, p. 42, supporting injectivity of this
    representation map. *)
Lemma symmetric_index_code_to_indices_injective n m :
  injective (@symmetric_index_code_to_indices n m).
Proof.
move=> x y h; apply: symmetric_index_decode_injective.
have hh := congr1 (@symmetric_indices_forget n m) h.
rewrite /symmetric_index_code_to_indices !symmetric_indices_boundK in hh.
exact (congr1 (fun a : symmetric_degree_indices n m => val a) hh).
Qed.

(** Source for [symmetric_index_code_to_indices_surjective]:
    Federer 1.9.2, p. 42, supporting surjectivity of this
    representation map. *)
Lemma symmetric_index_code_to_indices_surjective n m (a : symmetric_indices n m) :
  exists c, symmetric_index_code_to_indices c = a.
Proof.
have [c hc] := symmetric_index_decode_surjective (symmetric_indices_unbound_degree a).
exists c; apply: (can_inj (@symmetric_indices_forgetK n m)).
rewrite /symmetric_index_code_to_indices symmetric_indices_boundK.
apply: val_inj; exact: hc.
Qed.

(** Source for [symmetric_index_code_cardinality]: Federer
    1.9.2, p. 42, the recursive finite representation and
    Xi(n,m) have equal cardinalities. *)
Lemma symmetric_index_code_cardinality n m :
  #|symmetric_index_code n m| = #|{: symmetric_indices n m}|.
Proof.
rewrite -(card_codom (@symmetric_index_code_to_indices_injective n m)).
apply: eq_card=> a; apply/codomP.
have [c hc] := symmetric_index_code_to_indices_surjective a.
exists c; exact: esym hc.
Qed.
