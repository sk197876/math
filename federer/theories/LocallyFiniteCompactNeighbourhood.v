(** Federer (1969), 4.1.1, p. 345: a compact test support
    has an open neighbourhood meeting only finitely many
    partition supports. This supporting strengthening of compact
    incidence reuses the existing compact finite-cover theorem. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality topology.
From Federer Require Import LocallyFiniteFamilyUP CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [locally_finite_compact_open_neighbourhood]:
    one finite selection works throughout an open neighbourhood
    of a compact set, supporting the finite partition cutoffs
    in Federer 4.1.1, p. 345, from 3.1.13, p. 225. *)
Theorem locally_finite_compact_open_neighbourhood (X:topologicalType)
    (J:choiceType) (U:set X) (I:set J) (F:J->set X) (K:set X):
  open U -> is_locally_finite_family_on U I F ->compact K ->K `<=` U ->
  exists W:set X,open W /\ K `<=` W /\ W `<=` U /\
    finite_set (I `&` [set j|exists x,W x /\ F j x]).
Proof.
move=>hU hLocal hK hKU.
pose Hit (V:set X):=I `&` [set j|exists x,V x /\ F j x].
pose D:set (set X):=[set V|open V /\ V `<=` U /\ finite_set (Hit V)].
have hCover:K `<=` \bigcup_(V in D) V.
  move=>x hx; have [V [hV [hxV hFinite]]]:=hLocal x (hKU x hx).
  exists (V `&` U); last by split; [exact hxV|exact:hKU x hx].
  split; first exact:openI hV hU.
  split; first by move=>y [hy hu].
  apply:(sub_finite_set _ hFinite)=>j [hj [y [[hy hu] hFy]]].
  split; first exact hj; by exists y.
have [B hBD hBCover]:=@compact_open_finite_cover X [the choiceType of set X]
  D (fun V=>V) K hK (fun V hV=>hV.1) hCover.
have hB (V:set X) (hV:V \in B):D V.
  exact:(elimT (asboolP _) (hBD V hV)).
pose W:set X:=\bigcup_(V in [set` B]) V.
have hOpen:open W by apply:bigcup_open=>V hV; exact:(hB V hV).1.
have hKW:K `<=` W.
  move=>x hx; have [V hV hxV]:=hBCover x hx; by exists V.
have hWU:W `<=` U.
  move=>x [V hV hxV]; exact:(hB V hV).2.1 x hxV.
have hFinite:finite_set (\bigcup_(V in [set` B]) Hit V).
  apply:bigcup_finite; first exact:finite_fset.
  move=>V hV; exact:(hB V hV).2.2.
exists W; split=>//; split=>//; split=>//.
apply:(sub_finite_set _ hFinite)=>j [hj [x [[V hV hxV] hF]]].
exists V; first exact hV; split; first exact hj.
by exists x.
Qed.
