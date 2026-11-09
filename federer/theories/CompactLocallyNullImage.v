(** Federer (1969), 3.4.2(8), p. 315: assemble the
    null images of contained compact chart cubes. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import CompactFiniteCover MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_locally_null_image]: the cover assembly
    in 3.4.2(8), p. 315. Compactness of the original C
    permits a finite subcover of the local chart interiors.
    Only the outer-measure laws enter the image estimate; neither
    C nor any image piece is assumed measurable. *)
Theorem compact_locally_null_image (R:realType) (X:topologicalType) (Y:choiceType)
    (mu:set Y->\bar R) (f:X->Y) (C:set X):
  is_measure mu ->compact C ->
  (forall x,C x ->exists U:set X,open U /\U x /\mu (f @` (C `&` U))=0) ->
  mu (f @` C)=0.
Proof.
move=>hMu hC hLocal.
pose D:set (set X):=[set U|open U /\mu (f @` (C `&` U))=0].
have hCover:C `<=` \bigcup_(U in D) U.
  move=>x hx;have [U [hOpen [hMember hNull]]]:=hLocal x hx.
  exists U;[by split|exact:hMember].
have [F hFD hF]:=@compact_open_finite_cover X [the choiceType of set X] D (fun U=>U) C
  hC (fun U hU=>hU.1) hCover.
have hImage:f @` C `<=` \bigcup_(i:F) f @` (C `&` val i).
  move=>y [x hx <-];have [U hUF hxU]:=hF x hx.
  exists ([` hUF]%fset);first by [].
  by exists x;first split.
have hBound:=@measure_finite_indexed_cover R Y (F:finType) mu hMu
  (f @` C) (fun i:F=>f @` (C `&` val i)) hImage.
have hZero (i:F):mu (f @` (C `&` val i))=0.
  exact:(set_mem (hFD (val i) (valP i))).2.
rewrite (eq_bigr (fun _=>0) (fun i _=>hZero i)) big1 // in hBound.
apply/eqP;by rewrite eq_le hBound (measure_nonnegative hMu).
Qed.
