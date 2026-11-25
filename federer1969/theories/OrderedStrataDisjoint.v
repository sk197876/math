(** Federer (1969), corrected 3.4.8(11), p. 327,
    used in 3.4.10, p. 337: avoiding
    every earlier stratum implies pairwise disjointness. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ordered_strata_pairwise_disjoint]: the
    pairwise form of the corrected earlier-stratum
    condition, book p. 327 line 24,
    needed for the regular core in 3.4.10,
    p. 337. This is only an order
    connection, not a new decomposition theorem. *)
Theorem ordered_strata_pairwise_disjoint (X:Type) mu (P:set X)
    (S:'I_mu->set X):
  (forall i x,S i x ->~(P `|` \bigcup_(j in [set j:'I_mu|(j<i)%N]) S j) x) ->
  forall i j,i<>j ->forall x,S i x ->~S j x.
Proof.
move=>hEarlier i j hDifferent x hxI hxJ.
case:(ltngtP (i:nat) (j:nat))=>hOrder.
- apply:(hEarlier j x hxJ);right;exists i;[exact:hOrder|exact:hxI].
- apply:(hEarlier i x hxI);right;exists j;[exact:hOrder|exact:hxJ].
- apply:hDifferent;exact:val_inj hOrder.
Qed.
