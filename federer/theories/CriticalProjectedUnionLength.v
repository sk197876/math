(** Federer (1969), 3.3.20, p. 307, as corrected
    by published erratum p. 6, book p. 307 line 26. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import LebesgueScalarMeasure BinaryProjectedIntervalOverlap
  ClosedSegmentOverlapUnion OrderedSegmentUnionLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_projected_union_length]:
    both exact first-level projected-length formulas
    of 3.3.20, p. 307, published
    erratum p. 6, book p. 307
    line 26. The four original intervals merge
    into two or three ordered closed intervals.
    Every common endpoint is retained and proved null. *)
Theorem critical_original_projected_union_length (R:realType) (u v:R):
  0<=v ->v<=u ->
  lebesgue_scalar_measure (binary_projected_interval_union (1/4:R) u v)=
    (if v<=u/2 then 2*(u/4+v) else 3*u/2)%:E.
Proof.
move=>hv hvu.
have hu:0<=u:=le_trans hv hvu.
case:ifP=>hBranch.
- have hLeft:((`[0,(1/4:R)*(u+v)] `|` `[(1-1/4)*v,(1/4)*u+v]):set R)=
      `[0,u/4+v].
    have h:=@closed_segment_overlap_union R 0 ((1/4)*(u+v)) ((1-1/4)*v) ((1/4)*u+v).
    have h0:0<=(1-1/4)*v by nra.
    have h1:(1-1/4)*v<=(1/4)*(u+v) by nra.
    have h2:(1/4)*(u+v)<=(1/4)*u+v by nra.
    have hEnd:(1/4:R)*u+v=u/4+v by field.
    by rewrite -hEnd;exact:h h0 h1 h2.
  have hRight:((`[(1-1/4:R)*u,u+(1/4)*v] `|` `[(1-1/4)*(u+v),u+v]):set R)=
      `[(3/4)*u,u+v].
    have h0:(1-1/4:R)*u<=(1-1/4)*(u+v) by nra.
    have h1:(1-1/4:R)*(u+v)<=u+(1/4)*v by nra.
    have h2:u+(1/4:R)*v<=u+v by nra.
    have h:=@closed_segment_overlap_union R ((1-1/4)*u) (u+(1/4)*v) ((1-1/4)*(u+v)) (u+v) h0 h1 h2.
    have hStart:(1-1/4:R)*u=(3/4)*u by field.
    by rewrite -hStart;exact:h.
  have hUnion:binary_projected_interval_union (1/4:R) u v=
      ((`[0,u/4+v] `|` `[(3/4)*u,u+v]):set R).
    by rewrite /binary_projected_interval_union -hLeft -hRight !setUA.
  have h0:0<=u/4+v by nra.
  have h1:u/4+v<=(3/4)*u by nra.
  have h2:(3/4)*u<=u+v by nra.
  rewrite hUnion (scalar_lebesgue_two_ordered_segments h0 h1 h2).
  congr (_%:E);field;by rewrite ?pnatr_eq0.
- have hBranchR:u/2<v by rewrite ltNge hBranch.
  have hMiddle:((`[(1-1/4:R)*v,(1/4)*u+v] `|` `[(1-1/4)*u,u+(1/4)*v]):set R)=
      `[(3/4)*v,u+v/4].
    have h0:(1-1/4:R)*v<=(1-1/4)*u by nra.
    have h1:(1-1/4:R)*u<=(1/4)*u+v by nra.
    have h2:(1/4:R)*u+v<=u+(1/4)*v by nra.
    have h:=@closed_segment_overlap_union R ((1-1/4)*v) ((1/4)*u+v) ((1-1/4)*u) (u+(1/4)*v) h0 h1 h2.
    have hStart:(1-1/4:R)*v=(3/4)*v by field.
    have hEnd:u+(1/4:R)*v=u+v/4 by field.
    by rewrite -hStart -hEnd;exact:h.
  have hUnion:binary_projected_interval_union (1/4:R) u v=
      ((`[0,(1/4)*(u+v)] `|` `[(3/4)*v,u+v/4] `|` `[(1-1/4)*(u+v),u+v]):set R).
    by rewrite /binary_projected_interval_union -hMiddle !setUA.
  have h0:0<=(1/4:R)*(u+v) by nra.
  have h1:(1/4:R)*(u+v)<=(3/4)*v by nra.
  have h2:(3/4:R)*v<=u+v/4 by nra.
  have h3:u+v/4<=(1-1/4:R)*(u+v) by nra.
  have h4:(1-1/4:R)*(u+v)<=u+v by nra.
  rewrite hUnion (scalar_lebesgue_three_ordered_segments h0 h1 h2 h3 h4).
  congr (_%:E);field;by rewrite ?pnatr_eq0.
Qed.
