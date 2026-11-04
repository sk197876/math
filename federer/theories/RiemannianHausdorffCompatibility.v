(** Federer (1969), 3.2.46, p. 281: the original-rho
    Hausdorff covering specification is realised by the finite
    technical carrier. Exact small diameters and costs, rather
    than an asserted nonlinear metric invariance, prove this. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier RiemannianDiameter
  RiemannianDiameterCompatibility RiemannianHausdorffUP MetricDiameter MetricRealPowerCost
  HausdorffLengthUP MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleEnvelope
  CaratheodoryLimitUP MetricRealPowerMeasureUP RealHausdorffMeasure
  RealHausdorffNormalisation NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_subunit_metric_cutoff]: sufficiently
    small finite positive cutoffs are cofinal among all positive
    cutoffs in 2.10.1, p. 170, supporting 3.2.46, p. 281. *)
Lemma positive_subunit_metric_cutoff (R : realType) (delta : \bar R) :
  (0<delta)%E -> exists r : R, 0<r<1 /\ (r%:E<=delta)%E.
Proof.
case: delta=> [d| |] hd.
- rewrite lte_fin in hd.
  exists (Order.min (d/2) (1/2)); split.
  + apply/andP; split.
    * by rewrite lt_min !divr_gt0 // !ltr0n.
    * have hHalf : Order.min (d/2) (1/2) <= 1/2 by rewrite ge_min lexx orbT.
      apply: le_lt_trans hHalf _; clear; lra.
  + rewrite lee_fin; apply: le_trans _ (_ : d/2 <= d); last by clear -hd; lra.
    by rewrite ge_min lexx.
- exists (1/2); split; last exact: leey.
  apply/andP; split; clear; lra.
- by [].
Qed.

Section Compatibility.
Context (R : realType) n A g (hg : @is_continuous_riemannian_tensor R n A g).
Local Notation M := [the metricType R of riemannian_metric_space hg].
Local Notation J := (@nonempty_metric_sets R M).
Variables (c p delta : R).

(** Source for [riemannian_small_cover_cost]: each admissible
    countable cover has the exact same total cost for original
    rho and its finite carrier, including degree zero and
    infinite sums, supporting 3.2.46, p. 281. *)
Lemma riemannian_small_cover_cost (G : set J) :
  delta<1 ->
  (forall j, G j -> (extended_metric_diameter (val j)<=delta%:E)%E) ->
  nonnegative_sum G (fun j=>metric_real_power_cost c p (riemannian_diameter hg (val j))) =
  nonnegative_sum G (fun j=>metric_real_diameter_cost c p (val j)).
Proof.
move=> hDelta hCut; apply: nonnegative_sum_ext=> j hj.
by rewrite /metric_real_diameter_cost (riemannian_small_diameter_equal (hCut j hj) hDelta).
Qed.

(** Source for [riemannian_scale_as_metric]: original-rho
    covering laws imply the finite-carrier covering laws at
    every cutoff below one, supporting 3.2.46, p. 281. *)
Lemma riemannian_scale_as_metric (nu : set M -> \bar R) :
  delta<1 -> is_riemannian_hausdorff_scale hg c p delta nu ->
  @is_metric_scale_envelope R M J (fun j=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) delta%:E nu.
Proof.
move=> hDelta hNu; constructor.
- move=> B G hCount hCut hCover.
  rewrite -(riemannian_small_cover_cost hDelta hCut).
  apply: (riemannian_hausdorff_scale_lower hNu hCount _ hCover)=> j hj.
  rewrite (riemannian_small_diameter_cutoff (val j) hDelta); exact: hCut j hj.
- move=> B b hBound.
  apply: (riemannian_hausdorff_scale_greatest hNu)=> G hCount hCut hCover.
  have hCap j (hj : G j) : (extended_metric_diameter (val j)<=delta%:E)%E.
    by rewrite -(riemannian_small_diameter_cutoff (val j) hDelta); exact: hCut j hj.
  rewrite (riemannian_small_cover_cost hDelta hCap).
  exact: hBound G hCount hCap hCover.
Qed.

(** Source for [metric_scale_as_riemannian]: the converse
    small-scale compatibility uses the identical original
    diameters and costs, supporting 3.2.46, p. 281. *)
Lemma metric_scale_as_riemannian (nu : set M -> \bar R) :
  delta<1 ->
  @is_metric_scale_envelope R M J (fun j=>val j)
    (fun j=>metric_real_diameter_cost c p (val j)) delta%:E nu ->
  is_riemannian_hausdorff_scale hg c p delta nu.
Proof.
move=> hDelta hNu; constructor.
- move=> B G hCount hCut hCover.
  have hCap j (hj : G j) : (extended_metric_diameter (val j)<=delta%:E)%E.
    by rewrite -(riemannian_small_diameter_cutoff (val j) hDelta); exact: hCut j hj.
  rewrite (riemannian_small_cover_cost hDelta hCap).
  exact: (metric_scale_envelope_lower hNu hCount hCap hCover).
- move=> B b hBound; apply: (metric_scale_envelope_greatest hNu)=> G hCount hCut hCover.
  rewrite -(riemannian_small_cover_cost hDelta hCut).
  apply: (hBound G hCount _ hCover)=> j hj.
  rewrite (riemannian_small_diameter_cutoff (val j) hDelta); exact: hCut j hj.
Qed.
End Compatibility.

(** Source for [riemannian_hausdorff_carrier_laws]: all original
    rho Hausdorff infima and their limiting supremum agree
    with the finite technical carrier, Federer 3.2.46, p. 281.
    Real degrees, actual Gamma costs and infinite masses remain. *)
Theorem riemannian_hausdorff_carrier_laws (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p) :
  is_riemannian_hausdorff_measure hg p hp
    (@real_hausdorff_measure R [the metricType R of riemannian_metric_space hg] p hp).
Proof.
pose M := [the metricType R of riemannian_metric_space hg].
pose J := @nonempty_metric_sets R M.
pose c := real_hausdorff_normalisation hp.
pose S := fun j : J=>val j.
pose cost := fun j : J=>metric_real_diameter_cost c p (val j).
have hMu := @real_hausdorff_measure_specification R M p hp.
constructor.
- move=> B delta nu /andP [h0 h1] hNu.
  have hCap := riemannian_scale_as_metric h1 hNu.
  have hPositive : (0<delta%:E)%E by rewrite lte_fin.
  exact (@caratheodory_limit_upper R M J S cost _ hMu B delta%:E nu hPositive hCap).
- move=> B b hBound; apply: (caratheodory_limit_least hMu)=> delta nu hDelta hNu.
  have [r [/andP [hr0 hr1] hrDelta]] := positive_subunit_metric_cutoff hDelta.
  pose xi := @metric_scale_envelope R M J S cost r%:E.
  have hXi := @metric_scale_envelope_specification R M J S cost r%:E.
  have hRhoXi := metric_scale_as_riemannian hr1 hXi.
  have hSmall : 0<r<1 by apply/andP; split.
  apply: le_trans _ (hBound r xi hSmall hRhoXi).
  exact: metric_scale_envelope_antitone_cutoff hXi hNu hrDelta B.
Qed.

(** Source for [riemannian_hausdorff_measure_unique]: the
    original covering and supremum laws determine one measure,
    supporting Federer 3.2.46, p. 281. *)
Lemma riemannian_hausdorff_measure_unique (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) hp mu nu :
  is_riemannian_hausdorff_measure hg p hp mu ->
  is_riemannian_hausdorff_measure hg p hp nu -> forall B, mu B=nu B.
Proof.
move=> hMu hNu B; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (riemannian_hausdorff_limit_least hMu)=> delta xi hDelta hXi.
  exact (@riemannian_hausdorff_limit_upper R n A g hg p hp nu hNu B delta xi hDelta hXi).
- apply: (riemannian_hausdorff_limit_least hNu)=> delta xi hDelta hXi.
  exact (@riemannian_hausdorff_limit_upper R n A g hg p hp mu hMu B delta xi hDelta hXi).
Qed.
