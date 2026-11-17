(** Federer (1969), 3.4.8(10), p. 332:
    finitely many strict fibre-coordinate inequalities
    persist near the original fibre. This
    general topology connection uses open scalar
    rays and continuity, not a new calculus theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From mathcomp.analysis.normedtype_theory Require Import num_normedtype.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_strict_order_neighbourhood]:
    the strict order of omega_(m+1)
    on two local inverse branches persists,
    supporting 3.4.8(10), p. 332.
    The midpoint gives disjoint scalar rays;
    arbitrary topological source spaces remain allowed. *)
Theorem continuous_strict_order_neighbourhood (R:realType) (T:topologicalType)
    (f g:T->R) (y:T):
  {for y,continuous (fun z:T=>(f z:real_line_metric R))} ->
  {for y,continuous (fun z:T=>(g z:real_line_metric R))} ->f y<g y ->
  nbhs y [set z|f z<g z].
Proof.
move=>hF hG hOrder.
pose c:R:=(f y+g y)/2.
have hFC:f y<c by rewrite /c;lra.
have hCG:c<g y by rewrite /c;lra.
have hFOpen:@open (real_line_metric R) [set t|t<c].
  change (open [set t:R^o|t<c]);exact:open_lt.
have hGOpen:@open (real_line_metric R) [set t|c<t].
  change (open [set t:R^o|c<t]);exact:open_gt.
have hFNear:nbhs (f y:real_line_metric R) [set t|t<c].
  rewrite openE in hFOpen;exact:hFOpen (f y) hFC.
have hGNear:nbhs (g y:real_line_metric R) [set t|c<t].
  rewrite openE in hGOpen;exact:hGOpen (g y) hCG.
have hPreF:nbhs y [set z|f z<c]:=hF _ hFNear.
have hPreG:nbhs y [set z|c<g z]:=hG _ hGNear.
apply:filterS (filterI hPreF hPreG)=>z [hBelow hAbove].
exact:lt_trans hBelow hAbove.
Qed.
