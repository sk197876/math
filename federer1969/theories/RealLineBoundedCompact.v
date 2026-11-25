(** Federer (1969), 2.10.21, p. 183: apply compactness of anchored Lipschitz
    families to the real-valued distance profiles. Compactness of real
    closed bounded intervals is general-topology background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MetricClosedBalls LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_line_boundedly_compact]: supporting
    real-valued instance of the bounded compactness
    hypothesis in 2.10.21, p. 183. *)
Lemma real_line_boundedly_compact (R : realType) :
  metric_boundedly_compact [the metricType R of real_line_metric R].
Proof.
move=> b r hr.
have he : @metric_closed_ball R [the metricType R of real_line_metric R] b r=`[b-r,b+r].
  apply/seteqP; split=> x hx.
  - have h : `|b-x|<=r := hx.
    move: h; rewrite ler_norml=> /andP [h1 h2]; rewrite /mkset in_itv /=; apply/andP; split; lra.
  - have /andP [h1 h2] : (b-r<=x<=b+r) by move: hx; rewrite /mkset in_itv /=.
    change (is_true (`|b-x|<=r)); rewrite ler_norml; apply/andP; split; lra.
rewrite he; exact: segment_compact.
Qed.
