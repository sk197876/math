(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureDerivationContext MeasureDerivates
  NullBallLocus CenteredBallRatioDomain CenteredBallRelations CoveringRelationUP
  CoveringRelationLimits CoveringFiniteLimitBounds MetricClosedBalls MetricDiameterUP
  MetricDiameter ExtendedRealBounds PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_right_infinite_real_thresholds]: supporting
    order criterion for the radial infinite limit in Federer
    2.9.15, p. 160. Finite real thresholds are cofinal
    below positive infinity. This expands the existing order-
    neighbourhood definition; it is not a separate book claim. *)
Lemma positive_right_infinite_real_thresholds (R : realType) (u : R -> \bar R) :
  positive_right_extended_order_limit u +oo <->
    forall c : R, exists d : R, (0<d)%R /\
      forall r, (0<r)%R -> (r<d)%R -> c%:E<u r.
Proof.
split; first by move=> [hl _] c; exact: hl c%:E (ltry c).
move=> h; split.
- move=> a; case: a=> [c| |] ha.
  + exact: h c.
  + by move: ha; rewrite ltxx.
  + have [d [hd hb]] := h 0%R; exists d; split=> // r hr hrd.
    exact: lt_trans (ltNyr 0%R) (hb r hr hrd).
- by move=> b; rewrite ltNge leey.
Qed.

(** Source for [infinite_centered_derivate_radius_bounds]: supporting
    conversion of the centered-ball derivate to the radial limit
    in Federer 2.9.15, p. 160. Finite lower thresholds
    on the infinite covering limit bound all sufficiently small
    radius ratios. A ball's diameter is bounded by twice its
    radius, without requiring equality. *)
Lemma infinite_centered_derivate_radius_bounds (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (x : X) :
  is_derivation_measure phi ->
  partial_function_graph (measure_derivate psi phi (@centered_closed_ball_relation R X)) x +oo ->
  ~ measure_null_ball_points phi x /\ forall c : R, exists d : R,
    (0<d)%R /\ forall r, (0<r)%R -> (r<d)%R ->
      c%:E<psi (metric_closed_ball x r)/phi (metric_closed_ball x r).
Proof.
move=> hphi hD.
have hn := @centered_derivate_outside_null_ball_points R X phi psi x +oo
  (derivation_measure_law hphi) hD.
split=> // c.
have hl : c%:E<covering_lower_limit (@centered_closed_ball_relation R X)
    (measure_ratio_function psi phi) x by rewrite hD.2.2; exact: ltry.
have [b [hb hinf]] := (covering_lower_limit_gt_iff _ _ x c%:E).1 hl.
exists (b/3)%R; split; first by rewrite divr_gt0 // ltr0n.
move=> r hr hrb.
have hdiam : extended_metric_diameter (metric_closed_ball x r)<b%:E.
  have hbound : extended_metric_diameter (metric_closed_ball x r)<=(r+r)%R%:E.
    apply: (metric_diameter_least (extended_metric_diameter_specification _)).
    + rewrite lee_fin; exact: addr_ge0 (ltW hr) (ltW hr).
    + move=> y z hy hz; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hy hz.
  apply: le_lt_trans hbound _; rewrite lte_fin; by lra.
have hq := @centered_ball_ratio_positive_domain R X phi psi x r hphi hn hr.
apply: lt_le_trans hinf (extended_real_inf_lower _).
exists (metric_closed_ball x r); split; first by exists r.
by split.
Qed.

(** Source for [radius_bounds_infinite_centered_derivate]: converse
    radial conversion for Federer 2.9.15, p. 160. A small-
    diameter centered ball is represented by a sufficiently small
    radius using 2.8.18's radius-representation lemma. This handles
    singleton balls and isolated points, for which arbitrary
    radius representations cannot be bounded by their diameters. *)
Lemma radius_bounds_infinite_centered_derivate (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (x : X) :
  is_derivation_measure phi -> ~ measure_null_ball_points phi x ->
  (forall c : R, exists d : R, (0<d)%R /\ forall r,
    (0<r)%R -> (r<d)%R -> c%:E<psi (metric_closed_ball x r)/phi (metric_closed_ball x r)) ->
  partial_function_graph (measure_derivate psi phi (@centered_closed_ball_relation R X)) x +oo.
Proof.
move=> hphi hn hbounds.
pose V := @centered_closed_ball_relation R X.
pose f := measure_ratio_function psi phi.
have hdf := @centered_ratio_domain_fine R X phi psi x hphi hn.
have hfinite c : c%:E<=covering_lower_limit V f x.
  have [d [hd hbd]] := hbounds c.
  pose t := (d/2)%R.
  have ht : (0<t)%R by rewrite /t divr_gt0 // ltr0n.
  have htd : (t<d)%R by rewrite /t; lra.
  apply: le_trans _ (@covering_lower_limit_ge_level R X V f x t ht).
  apply: extended_real_inf_greatest=> y [S [hS [hdiam hy]]].
  have [r [hr hSr]] := hS.
  have hdiamB : extended_metric_diameter (metric_closed_ball x r)<t%:E by rewrite -hSr.
  have heq := @closed_ball_small_radius_representation R X x r t hr ht hdiamB.
  have hsmall : S=metric_closed_ball x (Num.min r t) by rewrite hSr heq.
  have hrs : (0<Num.min r t)%R by rewrite lt_min hr ht.
  have hsdt : (Num.min r t<d)%R.
    apply: le_lt_trans _ htd; by rewrite ge_min lexx orbT.
  rewrite hsmall in hy.
  have hq := @centered_ball_ratio_positive_domain R X phi psi x (Num.min r t) hphi hn hrs.
  have hey := partial_function_single_valued hy hq.
  rewrite hey; exact: ltW (hbd _ hrs hsdt).
have hl : covering_lower_limit V f x=+oo.
  case heq: (covering_lower_limit V f x)=> [a| |] //.
  - have hh := hfinite (a+1)%R; rewrite heq lee_fin in hh.
    have ha : (a<a+1)%R by rewrite ltrDl ltr01.
    by have := lt_le_trans ha hh; rewrite ltxx.
  - by have := hfinite 0%R; rewrite heq.
have hord := @covering_limits_ordered R X V f x hdf.
have hu : covering_upper_limit V f x=+oo.
  apply/eqP; by rewrite eq_le leey /= -hl.
split; first exact: centered_closed_balls_fine.
by split.
Qed.

(** Source for [measure_infinite_centered_density_points]: direct
    set W in Federer 2.9.15, p. 160. The positive-right
    order limit expresses the literal radius limit. Exclusion
    of P preserves ordinary partial division: outside P every
    positive-radius denominator is positive and finite in M,
    while at P all sufficiently small quotients are undefined. *)
Definition measure_infinite_centered_density_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) : set X :=
  [set x | ~ measure_null_ball_points phi x /\
    positive_right_extended_order_limit
      (fun r : R => psi (metric_closed_ball x r)/phi (metric_closed_ball x r)) +oo].

(** Source for [infinite_centered_density_derivate]: direct
    identification of the radial set W with the infinite
    centered-ball derivate in Federer 2.9.15, p. 160,
    first proof paragraph. All assertions use actual quotient
    values; the proof explicitly treats the null-ball locus. *)
Theorem infinite_centered_density_derivate (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (x : X) :
  is_derivation_measure phi ->
  (measure_infinite_centered_density_points psi phi x <->
    partial_function_graph (measure_derivate psi phi (@centered_closed_ball_relation R X)) x +oo).
Proof.
move=> hphi; split.
- move=> [hn hl].
  have hb := (positive_right_infinite_real_thresholds _).1 hl.
  exact: radius_bounds_infinite_centered_derivate hphi hn hb.
- move=> hd; have [hn hb] := infinite_centered_derivate_radius_bounds hphi hd.
  split=> //; exact: (positive_right_infinite_real_thresholds _).2 hb.
Qed.
