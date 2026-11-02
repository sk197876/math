(** Federer (1969), 1.6.5, p. 26, the remaining factors after
    contraction of an initial block. Supporting index identities
    for the dual-basis formula of 1.5.2, pp. 22-23. These are
    bookkeeping lemmas, not additional claims printed in the book. *)

From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [initial_complement_sequence]: Federer 1.6.5,
    p. 26, retention of the factors after the initial contracted
    block. Supporting identity: the increasing complement of the
    first n indices in n+r is the list n,...,n+r-1. *)
Lemma initial_complement_sequence n r :
  val (val (top_complement (Lambda_initial (leq_addr r n)))) =
    [seq rshift n i | i <- enum 'I_r].
Proof.
apply: (@irr_sorted_eq _ (fun i j : 'I_(n+r) => i < j)).
- move=> i j k; exact: ltn_trans.
- by move=> i; rewrite ltnn.
- have := valP (top_complement (Lambda_initial (leq_addr r n))).
  by rewrite sorted_map.
- suff : sorted ltn (map val [seq rshift n i | i <- enum 'I_r]).
    by rewrite sorted_map.
  rewrite -map_comp.
  change (sorted ltn [seq n + val i | i <- enum 'I_r]).
  rewrite (map_comp (addn n) val) val_enum_ord -iotaDl addn0.
  exact: iota_ltn_sorted.
- move=> i.
  have hi : (i \in val (val (top_complement (Lambda_initial (leq_addr r n))))) = (n <= i).
    have hh : (i \in Lambda_set (top_complement (Lambda_initial (leq_addr r n)))) = (n <= i).
      by rewrite /top_complement nu_image in_setD initial_set_mem Lambda_top_set in_setT andbT -leqNgt.
    by move: hh; rewrite /Lambda_set inE.
  rewrite hi; apply/idP/mapP.
  + move=> hni.
    have hir : i-n < r by rewrite (ltn_subLR r hni); exact: ltn_ord.
    exists (Ordinal hir); first exact: mem_enum.
    by apply: val_inj; rewrite /= subnKC.
  + move=> [j _ ->]; exact: leq_addr.
Qed.
