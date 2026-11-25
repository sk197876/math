(** Federer (1969), 3.4.8(11), p. 333:
    local finiteness of components near each
    point gives finiteness near a compact set.
    This supporting topology lemma reuses the
    project's compact finite-cover theorem. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality topology.
From Federer Require Import CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_local_component_finiteness]:
    the compact-ball step for the critical
    variety H in 3.4.8(11), p. 333.
    Count the actual ambient components which
    meet the given compact set. *)
Theorem compact_local_component_finiteness (X:topologicalType) (A K:set X):
  compact K ->
  (forall a,K a ->exists U:set X,open U /\ U a /\
    finite_set (connected_component A @` (A `&` U))) ->
  finite_set (connected_component A @` (A `&` K)).
Proof.
move=>hK hLocal.
pose D:set (set X):=fun U=>open U /\ finite_set (connected_component A @` (A `&` U)).
have hCover:K `<=` \bigcup_(U in D) U.
  move=>a ha;have [U [hU [hUa hFinite]]]:=hLocal a ha.
  by exists U;first split.
have [F hFD hFCover]:=@compact_open_finite_cover X [the choiceType of (set X)]
  D (fun U=>U) K hK (fun U hU=>hU.1) hCover.
pose B:=\bigcup_(U in [set` F]) (connected_component A @` (A `&` U)).
have hB:finite_set B.
  apply:bigcup_finite;first exact:finite_fset.
  move=>U hU;have /asboolP hDU:=hFD U hU;exact:hDU.2.
apply:(sub_finite_set _ hB)=>C [x [hAx hKx] <-].
have [U hUF hUx]:=hFCover x hKx.
exists U;first exact:hUF.
by exists x;first split.
Qed.
