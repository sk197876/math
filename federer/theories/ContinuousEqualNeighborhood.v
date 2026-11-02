(** General-topology support for the compact-cover density argument in
    Federer (1969), 2.6.6, pp. 120–121. Kelley, General Topology, Dover 2017
    reprint of 1955, 7.R(a)(iii), pp. 244–245, uses neighbourhoods where two
    continuous functions agreeing at a point differ by less than a
    prescribed positive error. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_equal_uniform_neighborhood]: supporting
    neighbourhood step in Kelley 7.R(a)(iii), pp. 244–245,
    for the density used in Federer 2.6.6, pp. 120–121. *)
Lemma continuous_equal_uniform_neighborhood (R : realType) (X : topologicalType)
    (f g : X -> R) (x : X) (e : R) :
  continuous (f : X -> real_line_metric R) -> continuous (g : X -> real_line_metric R) ->
  f x=g x -> 0<e -> nbhs x [set y | `|f y-g y|<e].
Proof.
move=> hf hg heq he.
have hc : continuous (fun y : X=>(f y-g y : real_line_metric R)).
  move=> y; exact: (@continuousB R R^o X f g y (hf y) (hg y)).
have hn := hc x _ (@nbhsx_ballx R (real_line_metric R) (f x-g x) e he).
rewrite heq subrr in hn.
apply: (@filterS X (nbhs x) (nbhs_filter x) _ _ _ hn)=> y hy.
by move: hy; rewrite /preimage real_line_ball_distance /= sub0r normrN.
Qed.
