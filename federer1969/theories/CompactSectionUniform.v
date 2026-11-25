(** Federer (1969), 2.6.4, p. 119: supporting local uniform continuity of
    sections over a compact set, used for the product Daniell functional.
    This follows from the tube lemma of general topology. The narrow
    norm-continuity import concerns only real topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module pseudometric_normed_Zmodule.
From Federer Require Import RealMetricBackground TopologicalProductMaps CompactTube CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_sections_locally_uniform]: supporting
    uniform control of h(x,y)-h(x,b) for x in a fixed
    compact set and y near b, in Federer 2.6.4,
    p. 119. Empty compact sets are allowed. *)
Theorem compact_sections_locally_uniform (R : realType) (X Y : topologicalType)
    (h : (X*Y) -> R) (K : set X) (b : Y) (e : R) :
  continuous (h : (X*Y) -> real_line_metric R) -> compact K -> 0<e ->
  exists V : set Y, open V /\ V b /\ forall y x, V y -> K x -> `|h (x,y)-h (x,b)|<e.
Proof.
move=> hh hK he.
have hc1 : continuous (fun p : Y*X => (p.2,p.1)).
  apply: topological_pair_continuous; [exact: second_projection_continuous|exact: first_projection_continuous].
have hc2 : continuous (fun p : Y*X => (p.2,b)).
  apply: topological_pair_continuous; [exact: second_projection_continuous|exact: cst_continuous].
have hd : continuous (fun p : Y*X => (h (p.2,p.1)-h (p.2,b) : real_line_metric R)).
  move=> p; apply: (@continuousB R R^o (Y*X)%type _ _ p).
  - exact: continuous_comp (hc1 p) (hh (p.2,p.1)).
  - exact: continuous_comp (hc2 p) (hh (p.2,b)).
have hn : continuous (fun p : Y*X => (`|h (p.2,p.1)-h (p.2,b)| : real_line_metric R)).
  move=> p; exact: continuous_comp (hd p) (@norm_continuous R R^o _).
pose O := [set p : Y*X | `|h (p.2,p.1)-h (p.2,b)|<e].
have ho : open O.
  exact ((@continuousP (Y*X)%type (real_line_metric R) _).1 hn
    [set r | r<e] (@order_strict_lower_ray_open _ [the orderTopologicalType _ of R^o] e)).
have hdis x : K x -> ~ (~` O) (b,x).
  move=> _ hnot; apply: hnot; rewrite /O /= subrr normr0; exact he.
have [V [W [hV [hW [hb [hKW hVW]]]]]] :=
  @compact_fiber_closed_tube Y X (~` O) K b (open_closedC ho) hK hdis.
exists V; split=> //; split=> // y x hy hx.
apply: contrapT=> hnO; exact (hVW y x hy (hKW x hx) hnO).
Qed.
