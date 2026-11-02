(** Federer (1969), 3.1.4, pp. 214–215: measurable radius cutoffs
    for small exceptional sections. Closed-ball bounds are used for
    these auxiliary cutoffs; they imply the printed open-ball bounds
    and have the same exhaustion at every point of density zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanClosedBallVolume
  EuclideanNoncenteredVitali MetricClosedBalls CenteredBallRelations
  PartialFunctionUP MeasureSetDensity ProductMeasure ProductSections
  EuclideanSectionMassMeasurable EuclideanZeroDensitySmallMass ExtendedRealReciprocalBounds
  MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section Cutoffs.
Variable R : realType.
Variables m k : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R k)).
Variable S : set (X*Y).
Variable c : R.

(** Source for [euclidean_small_mass_cutoff]: the section-mass
    cutoff in the definitions of B and C in Federer 3.1.4, p. 214.
    The index p represents the positive integer p+1. *)
Definition euclidean_small_mass_cutoff (p : nat) : set X :=
  [set x | forall r : R, 0<r -> r<(p.+1%:R)^-1 ->
    (euclidean_lebesgue_measure k (product_vertical_section S x `&`
      metric_closed_ball (0%R : Y) r)<=(c*r^+k)%:E)%E].

(** Source for [euclidean_small_mass_cutoff_measurable]: the
    measurability of B and C asserted in Federer 3.1.4, p. 215,
    from 3.1.3(1), with the fixed ball-volume constant cancelled. *)
Lemma euclidean_small_mass_cutoff_measurable p :
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k)) S ->
  measure_measurable (@euclidean_lebesgue_measure R m) (euclidean_small_mass_cutoff p).
Proof.
move=> hS.
have h := euclidean_small_section_mass_measurable
  (c / euclidean_unit_ball_volume R k) ((p.+1%:R)^-1) hS.
have hpos := (euclidean_unit_ball_volumeE R k).2.
have he : c / euclidean_unit_ball_volume R k * euclidean_unit_ball_volume R k=c.
  by rewrite divfK ?(gt_eqF hpos).
by rewrite he in h.
Qed.

(** Source for [euclidean_small_mass_cutoff_increasing]: the
    monotonicity in p and q asserted in Federer 3.1.4, p. 215. *)
Lemma euclidean_small_mass_cutoff_increasing p q :
  (p<=q)%N -> euclidean_small_mass_cutoff p `<=` euclidean_small_mass_cutoff q.
Proof.
move=> hpq x hx r hr hrq; apply: hx hr _.
apply: lt_le_trans hrq _.
rewrite lef_pV2.
- by rewrite ler_nat ltnS.
- by rewrite qualifE /= ltr0n.
- by rewrite qualifE /= ltr0n.
Qed.

(** Source for [euclidean_zero_density_has_small_mass_cutoff]:
    the exhaustion by radius cutoffs used for B and C in Federer
    3.1.4, p. 215. The exceptional section need not be measurable. *)
Lemma euclidean_zero_density_has_small_mass_cutoff x :
  0<c ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R k)
    (@centered_closed_ball_relation R [the metricType R of Y])
    (product_vertical_section S x)) (0%R : Y) 0%E ->
  exists p, euclidean_small_mass_cutoff p x.
Proof.
move=> hc hz.
have hv := (euclidean_unit_ball_volumeE R k).2.
have he : 0<c/euclidean_unit_ball_volume R k by rewrite divr_gt0.
have [d [hd hs]] := euclidean_zero_density_small_mass hz he.
have [p hp] := positive_reciprocal_nat_small hd.
exists p=> r hr hrp.
have hh := ltW (hs r hr (lt_trans hrp hp)).
by rewrite (euclidean_closed_ball_normalized_volume (0%R : Y) (ltW hr))
  -EFinM mulrA divfK ?(gt_eqF hv) in hh.
Qed.
End Cutoffs.
