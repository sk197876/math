(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals PartialFunctionUP MeasureUP
  MeasureBasic MeasureDerivationContext NullBallLocus CenteredRatioInfinity MetricClosedBalls
  CoveringFamilyLaws OpenBallMeasureComparison BallMeasureComparisonCorollaries
  ExtendedRealReciprocalBounds TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_ratio_below_points]: supporting open
    strict-comparison sets for the Borel assertion in Federer
    2.9.15, p. 160, using the second corollary of 2.9.14,
    p. 160. The radius belongs to the open interval (0,d). *)
Definition centered_ratio_below_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (t d : R) : set X :=
  ball_measure_comparison_points (fun S => t%:E*phi S) psi (real_open_interval 0 d).

(** Source for [centered_ratio_below_points_open]: supporting
    application of the lower-comparison corollary of Federer
    2.9.14, p. 160, to the Borel representation of W
    in 2.9.15 on the same page. Both measures belong to M. *)
Lemma centered_ratio_below_points_open (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (t d : R) :
  is_derivation_measure phi -> is_derivation_measure psi -> (0<t)%R ->
  open (centered_ratio_below_points psi phi t d).
Proof.
move=> hphi hpsi ht.
exact (@ball_measure_lower_comparison_open R X phi psi (real_open_interval 0 d) t
  hphi hpsi ht (@real_open_interval_open R 0%R d) (fun r hr => hr.1)).
Qed.

(** Source for [positive_ball_ratio_sublevel]: supporting
    equivalence between mass comparisons and actual quotients
    outside P in Federer 2.9.15, p. 160. Only the positive
    finite denominator uses M; the numerator can be arbitrary. *)
Lemma positive_ball_ratio_sublevel (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (x : X) (r t : R) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x -> (0<r)%R ->
  (psi (metric_closed_ball x r)/phi (metric_closed_ball x r)<t%:E) =
    (psi (metric_closed_ball x r)<t%:E*phi (metric_closed_ball x r)).
Proof.
move=> hphi hn hr; have hm := derivation_measure_law hphi.
have hp := @outside_null_ball_points_positive R X phi x r hm hn hr.
have hf : phi (metric_closed_ball x r) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact (@derivation_measure_bounded_finite R X phi hphi _
    (@covering_closed_ball_bounded R X x r (ltW hr))).
pose b := fine (phi (metric_closed_ball x r)).
have he : phi (metric_closed_ball x r)=b%:E by rewrite /b fineK.
have hb : (0<b)%R by move: hp; rewrite he lte_fin.
by rewrite he inver (gt_eqF hb) lte_pdivrMr.
Qed.

(** Source for [infinite_centered_density_countable_formula]:
    supporting countable Borel representation for W in Federer
    2.9.15, p. 160. Natural positive thresholds are cofinal,
    reciprocal positive radius cutoffs are coinitial, and the
    complement of each strict lower comparison imposes a closed
    lower bound on all sufficiently small actual ratios. *)
Lemma infinite_centered_density_countable_formula (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) :
  is_derivation_measure phi ->
  measure_infinite_centered_density_points psi phi =
    (\bigcap_n \bigcup_k (~` centered_ratio_below_points psi phi
      (n.+1%:R : R) ((k.+1%:R : R)^-1)%R)) `\` measure_null_ball_points phi.
Proof.
move=> hphi; apply/seteqP; split=> x.
- move=> [hn hl]; split=> // n _.
  have [d [hd hb]] := (positive_right_infinite_real_thresholds _).1 hl (n.+1%:R : R).
  have [k hk] := @positive_reciprocal_nat_small R d hd.
  exists k=> //; move=> [r [[hr hrk] hmass]].
  have hlt := hb r hr (lt_trans hrk hk).
  have hq : psi (metric_closed_ball x r)/phi (metric_closed_ball x r)<(n.+1%:R : R)%:E.
    by rewrite (@positive_ball_ratio_sublevel R X psi phi x r _ hphi hn hr).
  by have := lt_trans hlt hq; rewrite ltxx.
- move=> [hQ hn]; split=> //; apply: (positive_right_infinite_real_thresholds _).2=> c.
  pose n := Num.bound (Num.max c 0)%R.
  have hnon : (0<=Num.max c 0)%R by rewrite le_max lexx orbT.
  have hb : (Num.max c 0<n%:R)%R := archi_boundP hnon.
  have hcm : (c<=Num.max c 0)%R by rewrite le_max lexx.
  have hcn : (c<n.+1%:R)%R.
    apply: lt_le_trans (le_lt_trans hcm hb) _; by rewrite ler_nat leqnSn.
  have [k _ hk] := hQ n Logic.I.
  exists ((k.+1%:R : R)^-1)%R; split; first by rewrite invr_gt0 ltr0n.
  move=> r hr hrk.
  have hge : (n.+1%:R : R)%:E<=psi (metric_closed_ball x r)/phi (metric_closed_ball x r).
    rewrite leNgt; apply/negP=> hq; apply: hk.
    exists r; split; first by split.
    by rewrite -(@positive_ball_ratio_sublevel R X psi phi x r _ hphi hn hr).
  apply: lt_le_trans _ hge; by rewrite lte_fin.
Qed.

(** Source for [measure_infinite_centered_density_points_borel]:
    direct Borel assertion for W in Federer 2.9.15,
    p. 160. The countable formula uses the open-comparison
    corollary of 2.9.14 and the openness of P. It proves
    Borel measurability, beyond completed-measure measurability
    of a general derivate in 2.9.6. *)
Theorem measure_infinite_centered_density_points_borel (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  borel_set (measure_infinite_centered_density_points psi phi).
Proof.
move=> hphi hpsi; rewrite (@infinite_centered_density_countable_formula R X psi phi hphi).
apply: borel_set_difference.
- apply: borel_set_countable_intersection; [exact: countableP|by exists 0%N|].
  move=> n _; apply: borel_set_countable_union; first exact: countableP.
  move=> k _; apply: borel_set_complement; apply: open_borel_set.
  apply: centered_ratio_below_points_open hphi hpsi _; by rewrite ltr0n.
- exact: open_borel_set (measure_null_ball_points_open (derivation_measure_law hphi)).
Qed.
