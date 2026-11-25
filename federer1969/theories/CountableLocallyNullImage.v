(** General topology and outer-measure support for Federer
    (1969), 3.4.3, pp. 316–317: assemble the local
    estimates on the original arbitrary rank-threshold source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_locally_null_image]: the local-to-global
    assembly implicit in 3.4.3, p. 317. A countable
    open base gives a countable subcover of any original source,
    and outer subadditivity gives image nullity. No source,
    image, or local piece is assumed measurable. *)
Theorem countable_locally_null_image (R:realType) (X:topologicalType) (Y:choiceType)
    (mu:set Y->\bar R) (f:X->Y) (B:set X) (U:nat->set X):
  is_measure mu ->is_countable_open_base U ->
  (forall x,B x ->exists V:set X,open V /\V x /\mu (f @` (B `&` V))=0) ->
  mu (f @` B)=0.
Proof.
move=>hMu hBase hLocal.
pose C:set (set X):=[set V|open V /\mu (f @` (B `&` V))=0].
have hCover:B `<=` \bigcup_(V in C) V.
  move=>x hx;have [V [hV [hxV hNull]]]:=hLocal x hx.
  exists V;[by split|exact:hxV].
have [G [hGC [hCountable hG]]]:=@countable_base_open_subcover X U B C hBase
  (fun V (hV:C V)=>hV.1) hCover.
have hNull:=@measure_null_countable_union R Y [the choiceType of (set X:Type)]
  mu hMu G (fun V=>f @` (B `&` V)) hCountable (fun V hV=>(hGC V hV).2).
apply:(measure_null_subset hMu _ hNull).
move=>y [x hx <-];have [V hV hxV]:=hG x hx.
exists V;first exact:hV.
by exists x;first split.
Qed.
