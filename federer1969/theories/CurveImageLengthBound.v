(** Supporting Federer (1969), 2.10.13, p. 177: localise the
    finite-variation hypothesis and use the nonexpanding arc-length factor
    of 2.5.16, pp. 109–110. No relevant Federer erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength CurveLipschitzFactor
  HausdorffLength HausdorffLengthMaps HausdorffLengthRestrictedMaps HausdorffLengthReal
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_segment_image_length_bound]: supporting
    arc-length comparison in the proof of 2.10.13, p. 177,
    using 2.5.16, pp. 109–110, and H1=L1 on the real line,
    2.10.7, p. 175. Only finite variation is used here;
    continuity and multiplicity are not part of this image bound. *)
Lemma curve_segment_image_length_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g -> (a<=b)%R ->
  @hausdorff_length R Y (g @` `[a,b])<=curve_variation g a b.
Proof.
move=> hg hab.
pose s := arc_length g; pose H := arc_length_factor g.
have he : g @` `[a,b]=H @` (s @` `[a,b]).
  apply/seteqP; split=> y.
  - move=> [x hx <-]; exists (s x); first by exists x.
    exact: (@arc_length_factor_compose R Y g hg x).
  - move=> [z [x hx <-] <-]; rewrite /H /s arc_length_factor_compose //.
have hnon : @hausdorff_length R Y (H @` (s @` `[a,b]))<=
    @hausdorff_length R [the metricType R of real_line_metric R] (s @` `[a,b]).
  apply: (@hausdorff_length_nonexpanding_on R [the metricType R of real_line_metric R] Y H (s @` `[a,b]))=> z w [x hx <-] [t ht <-].
  rewrite real_line_metric_distanceE.
  apply: (@arc_length_factor_lipschitz R Y g hg); by [exists x|exists t].
have hsub : (s @` `[a,b] : set (real_line_metric R)) `<=` `[s a,s b].
  move=> z [x hx <-]; move: hx; rewrite /= !in_itv /= => /andP[hax hxb].
  by rewrite (arc_length_monotone hg hax) (arc_length_monotone hg hxb).
have hb := @measure_mono R [the metricType R of real_line_metric R] _
  (@hausdorff_length_is_measure R [the metricType R of real_line_metric R]) _ _ hsub.
rewrite (hausdorff_length_real_segment (arc_length_monotone hg hab))
  (@arc_length_increment R Y g hg a b hab) in hb.
rewrite he; exact: le_trans hnon hb.
Qed.
