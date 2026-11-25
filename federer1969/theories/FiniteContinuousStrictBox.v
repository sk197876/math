(** Federer (1969), 3.4.8(11), pp. 334–335:
    the finite strict prefix inequalities define
    an open set. Their weak counterparts
    hold on its closure. This connection
    uses general topology and the project's real rays. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_continuous_strict_box_open]:
    the original finite prefix neighbourhood V
    is open, 3.4.8(11), p. 335. *)
Theorem finite_continuous_strict_box_open (R:realType) (X:topologicalType) (I:finType)
    (D:set I) (q:I->X->R) (epsilon:I->R):
  (forall i,continuous (fun x:X=>(q i x:real_line_metric R))) ->
  open [set x|forall i,D i ->q i x<epsilon i].
Proof.
move=>hQ;rewrite openE=>x hx.
have hEach i:nbhs x [set y|D i ->q i y<epsilon i].
  case:(pselect (D i))=>hD.
  - have hRay:@open (real_line_metric R) [set t:R|t<epsilon i]:=order_strict_lower_ray_open _.
    have hPre:open [set y:X|q i y<epsilon i].
      exact:(@open_comp X (real_line_metric R) (fun y=>q i y)
        [set t:R|t<epsilon i] (fun y _=>hQ i y) hRay).
    have hNear:nbhs x [set y:X|q i y<epsilon i].
      move:hPre;rewrite openE;move=>hPre;exact:hPre x (hx i hD).
    apply:(filterS _ hNear)=>y hy _;exact:hy.
  - apply:(filterS _ (@filterT X (nbhs x) (nbhs_filter x)))=>y _ hDi.
    exfalso;exact:hD hDi.
have hAll:=@filter_forall X I (fun i=>[set y|D i ->q i y<epsilon i])
  (nbhs x) (nbhs_filter x) hEach.
apply:(filterS _ hAll)=>y hy;exact:hy.
Qed.

(** Source for [continuous_strict_box_closure_bound]:
    weak prefix inequalities on Clos V,
    3.4.8(11), p. 335. This closure
    assertion also permits an infinite index family. *)
Theorem continuous_strict_box_closure_bound (R:realType) (X:topologicalType) (I:Type)
    (D:set I) (q:I->X->R) (epsilon:I->R):
  (forall i,continuous (fun x:X=>(q i x:real_line_metric R))) ->
  forall x,closure [set y|forall i,D i ->q i y<epsilon i] x ->
    forall i,D i ->q i x<=epsilon i.
Proof.
move=>hQ x hClosure i hDi.
have hRay:@closed (real_line_metric R) [set t:R|t<=epsilon i].
  exact:order_closed_lower_ray_closed.
have hPre:closed [set y:X|q i y<=epsilon i].
  exact:(@preimage_closed X (real_line_metric R) (fun y=>q i y)
    [set t:R|t<=epsilon i] (fun y _=>hQ i y) hRay).
have hInclusion:[set y:X|forall j,D j ->q j y<epsilon j] `<=`
    [set y:X|q i y<=epsilon i].
  move=>y hy;exact:ltW (hy i hDi).
exact:(hPre x (@closureS X _ _ hInclusion x hClosure)).
Qed.
