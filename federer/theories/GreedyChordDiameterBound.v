(** Federer (1969), 2.10.39, printed p. 199: apply the box of 2.10.38 at
    small source diameters before passing to covering limits. This
    supporting bound controls every chosen side by the original source
    diameter using residual contraction. Source context:
    GreedyChordFrameLaws.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric GreedyChordFrameUP GreedyChordFrameLaws
  MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [greedy_chord_length_diameter_bound]: supporting
    shrinking-mesh control for the box covers in
    2.10.39, p. 199. Each projected selected chord
    is no longer than its original source chord. *)
Lemma greedy_chord_length_diameter_bound (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (D : greedy_chord_frame_data R n) (hD : is_greedy_chord_frame S D)
    (d : R) : (extended_metric_diameter S<=d%:E)%E ->
  forall i, greedy_chord_length D i<=d.
Proof.
move=> hd i.
pose v := greedy_chord_first D i-greedy_chord_second D i.
have hres := @greedy_chord_residual_norm_antitone R n S D hD 0 i v
  (leq0n i) (ltnW (ltn_ord i)).
rewrite (greedy_chord_selected_norm hD i) (greedy_chord_residual_zero_law hD) in hres.
have [ha hb] := greedy_chord_endpoints_law hD i.
have hpair := @metric_diameter_upper R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] S
  (extended_metric_diameter S) (extended_metric_diameter_specification S)
  (greedy_chord_first D i) (greedy_chord_second D i) ha hb.
have hh := le_trans hpair hd; rewrite inner_metric_distanceE lee_fin in hh.
exact: le_trans hres hh.
Qed.
