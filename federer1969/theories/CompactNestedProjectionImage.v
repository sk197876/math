(** Federer (1969), 3.3.20, p. 307:
    the original Cantor-square projection is the intersection
    of its actual compact level projections. *)
From mathcomp Require Import all_boot all_order boolp classical_sets reals topology.
From Federer Require Import CompactNestedIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_nested_continuous_image_intersection]:
    supporting original projection-limit identity in
    3.3.20, p. 307. A closed original
    projection fibre intersects every decreasing compact
    level, hence their actual intersection. Only the
    first level needs compactness. Empty intersections
    and noninjective projections are retained. *)
Theorem compact_nested_continuous_image_intersection (R:realType)
    (X:topologicalType) (Y:metricType R) (C:nat->set X) (f:X->Y):
  compact (C 0%N) ->(forall n,closed (C n)) ->
  (forall n m,(n<=m)%N ->C m `<=` C n) ->continuous f ->
  f @` (\bigcap_n C n)=\bigcap_n (f @` C n).
Proof.
move=>hCompact hClosed hDecrease hContinuous;apply/seteqP;split=>y.
- move=>[x hx <-] n _;exists x=>//;exact:hx n Logic.I.
- move=>hImages.
  pose D n:=C n `&` (f @^-1` [set y]).
  have hFibre:closed (f @^-1` [set y]).
    apply:(@preimage_closed X Y f [set y]);first by move=>x _;exact:hContinuous x.
    apply:accessible_closed_set1;apply:hausdorff_accessible;exact:metric_hausdorff.
  have hDCompact:compact (D 0%N):=compact_closedI hCompact hFibre.
  have hDClosed n:closed (D n):=closedI (hClosed n) hFibre.
  have hDDecrease n m:(n<=m)%N ->D m `<=` D n.
    move=>hnm x [hx hf];split=>//;exact:hDecrease n m hnm x hx.
  have hDNonempty n:D n !=set0.
    have [x hx hValue]:=hImages n Logic.I.
    exists x;by split.
  have [x hX]:=@compact_nested_nonempty_intersection X D hDCompact hDClosed hDDecrease hDNonempty.
  exists x;last exact:(hX 0%N Logic.I).2.
  move=>n _;exact:(hX n Logic.I).1.
Qed.
