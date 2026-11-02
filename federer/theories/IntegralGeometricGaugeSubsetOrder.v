(** Federer (1969), 3.2.36, p. 273: monotonicity of
    the actual projection gauge controls reverse convex-cover costs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  ProjectedVolumeMeasurability IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability
  NonnegativeExtendedNormOrder SuslinSetUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_subset_order]: the reverse
    cost comparison for the isometry assertion about Q_1 in Federer
    3.2.36, p. 273. Every actual projected image is monotone
    under source inclusion. The already proved exponent-norm order
    and positive beta normalization transfer that order to the actual
    gauge. This supporting order law permits every admissible exponent
    and Suslin sources, without boundedness or finite mass assumptions. *)
Lemma integral_geometric_gauge_subset_order (R:realType) n k (hkn:(k<=n)%N) t
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  1<=t ->is_suslin_set R A ->is_suslin_set R B ->A `<=` B ->
  @integral_geometric_gauge R n k hkn t A<=@integral_geometric_gauge R n k hkn t B.
Proof.
move=>ht hA hB hSubset.
pose P:=orthogonal_projection_metric_space R n k.
pose theta:=@orthogonal_projection_probability R n k hkn.
pose hTheta:=@theta_star_is_measure R n k hkn.
rewrite /integral_geometric_gauge.
apply:lee_wpmul2l.
- rewrite lee_fin invr_ge0; exact:ltW (@projection_beta_positive R n k hkn t ht).
- apply:(@nonnegative_extended_norm_almost_order R P theta hTheta
    (projected_volume_function (m:=k) A) (projected_volume_function (m:=k) B) t
    (projected_volume_function_nonnegative A) (projected_volume_function_nonnegative B) ht
    (@theta_star_projected_volume_measurable R n k hkn A hA)
    (@theta_star_projected_volume_measurable R n k hkn B hB)).
  apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta))=>p _.
  apply:(@measure_mono R (inner_metric_space (@euclidean_inner_productP R k))
    (@euclidean_lebesgue_measure R k) (euclidean_lebesgue_is_measure R k)).
  move=>y [x hx <-]; exists x=>//; exact:hSubset x hx.
Qed.
