(** Supporting endpoint limits in Federer (1969), 2.9.20, p. 166, final
    proof sentence. Relative continuity on the closed segment is used only
    within that segment. Source context: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [segment_continuity_epsilon_control]: supporting precise
    endpoint continuity used in Federer 2.9.20, p. 166 At any point of
    [a,b], sufficiently close points of the same segment have close values.
    No extension or continuity outside the segment is assumed. *)
Lemma segment_continuity_epsilon_control (R : realType) (g : R -> R)
    (a b x e : R) :
  {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_line_metric R)} ->
  a<=x -> x<=b -> 0<e -> exists d : R, 0<d /\ forall y : R,
    a<=y -> y<=b -> `|y-x|<d -> `|g y-g x|<e.
Proof.
move=> hc hax hxb he.
have hx : (`[a,b] : set (real_line_metric R)) x by rewrite /= in_itv /= hax hxb.
have hcx : (g : real_line_metric R -> real_line_metric R) @
    within (`[a,b] : set (real_line_metric R)) (nbhs (x : real_line_metric R)) -->
      (g x : real_line_metric R).
  exact: (subspace_continuousP _ _).1 hc x hx.
have hb : \forall y \near within (`[a,b] : set (real_line_metric R))
    (nbhs (x : real_line_metric R)), ball (g x : real_line_metric R) e (g y).
  exact: (cvg_ballP _ _).1 hcx e he.
change (nbhs (x : real_line_metric R)
  [set y | `[a,b] y -> ball (g x : real_line_metric R) e (g y)]) in hb.
have [d hd hcontrol] := (nbhs_ballP (x : real_line_metric R) _).1 hb.
exists d; split=> // y hay hyb hyx.
have hxy : ball (x : real_line_metric R) d y by rewrite /ball /= distrC.
have hy : (`[a,b] : set (real_line_metric R)) y by rewrite /= in_itv /= hay hyb.
have := hcontrol y hxy hy.
by rewrite /ball /= distrC.
Qed.
