(** Federer (1969), 3.3.20, pp. 308–309:
    exact finite index laws for the original reversed corner patterns. *)
From mathcomp Require Import all_boot.
From Federer Require Import CriticalCornerPairingPatternsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_corner_pattern_index_offsets]:
    each forward or reversed original pattern index has
    admissible actual corner offsets, supporting 3.3.20,
    pp. 308–309. This is a consequence
    of the independent finite list laws. *)
Lemma critical_corner_pattern_index_offsets n budget L:
  is_critical_corner_pairing_pattern n budget L ->forall t (i:'I_(size L)),
  let p:=nth (0,0) (if t then rev L else L) i in
  p.1 \in [::0;3;12;15] /\p.2 \in [::0;3;12;15].
Proof.
move=>[_ [_ [hAll _]]] t i p.
have hMember:p \in L.
  rewrite /p;clear p;case:t=>[|];last exact:mem_nth (ltn_ord i).
  rewrite -mem_rev;apply:mem_nth;by rewrite size_rev;exact:ltn_ord.
have /andP[h1 h2]:=(allP hAll _ hMember).
by split.
Qed.

(** Source for [critical_corner_pattern_index_budget]:
    each original forward/reversed pair satisfies the
    inward-coordinate budget in 3.3.20, pp. 308–309.
    The finite zip law gives the exact indexed assertion. *)
Lemma critical_corner_pattern_index_budget n budget L:
  is_critical_corner_pairing_pattern n budget L ->forall i:'I_(size L),
  ((nth (0,0) L i).1+(nth (0,0) L i).2+
    (nth (0,0) (rev L) i).1+(nth (0,0) (rev L) i).2<=budget)%N.
Proof.
move=>[_ [_ [_ hBudget]]] i.
have hIndex:(i<size (zip L (rev L)))%N by rewrite size_zip size_rev minnn;exact:ltn_ord.
have hPair:=allP hBudget _ (mem_nth ((0,0),(0,0)) hIndex).
by rewrite nth_zip ?size_rev // in hPair.
Qed.
