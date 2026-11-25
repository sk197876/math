(** Federer (1969), 3.4.2(7), p. 314: extract countably many
    cutting manifolds from their relative neighbourhoods. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_countable_cutting_family]: the use of
    separability at the end of 3.4.2(7), p. 314. A countable
    base gives a countable subcover by the ambient neighbourhoods.
    Choose each associated cutting set locally and retain only
    its intersection with C. Empty sets and an empty complement
    are included; no default cutting manifold is assumed. *)
Theorem critical_countable_cutting_family (T:topologicalType) (U:nat->set T)
    (C B:set T) (P:set T->Prop):
  is_countable_open_base U ->
  (forall a,C a ->~B a ->exists V:set T,P V /\V `&` C `<=` C `\` B /\
    exists N:set T,open N /\N a /\C `&` N `<=` V) ->
  exists D:set (set T),countable D /\
    (forall V,D V ->P V /\V `&` C `<=` C `\` B) /\
    C `\` B=\bigcup_(V in D) (V `&` C).
Proof.
move=>hBase hLocal.
pose Cover:set (set T):=[set N|open N /\exists V:set T,
  P V /\V `&` C `<=` C `\` B /\C `&` N `<=` V].
have hCover:C `\` B `<=` \bigcup_(N in Cover) N.
  move=>a [hc hn].
  have [V [hV [hAvoid [N [hN [haN hCN]]]]]]:=hLocal a hc hn.
  exists N;last exact:haN.
  split;first exact:hN.
  exists V;split;first exact:hV.
  by split;[exact:hAvoid|exact:hCN].
have [D [hD [hCount hUnion]]]:=@countable_base_open_subcover T U (C `\` B) Cover hBase
  (fun N hN=>hN.1) hCover.
have hExists N:exists V:set T,D N ->P V /\V `&` C `<=` C `\` B /\C `&` N `<=` V.
  case:(pselect (D N))=>[hDN|hNo].
  - have [hOpen [V hV]]:=hD N hDN;exists V;by move=>_.
  - exists set0;move=>hN;exact:False_ind _ (hNo hN).
have [V hV]:=choice hExists.
exists (V @` D);split.
- exact:(sub_countable (card_image_le _ _) hCount).
split.
- move=>W [N hN <-];exact:(conj (hV N hN).1 (hV N hN).2.1).
- apply/seteqP;split.
  + move=>x hx.
    have [N hN hxN]:=hUnion x hx.
    exists (V N);first by exists N.
    split;last exact:hx.1.
    exact:(hV N hN).2.2 x (conj hx.1 hxN).
  + move=>x [W [N hN <-] [hxV hxC]].
    exact:(hV N hN).2.1 x (conj hxV hxC).
Qed.
