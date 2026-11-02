(** Federer (1969), 3.1.8, pp. 217–218: overlapping
    equal-radius balls leave a point outside two small exceptional sets.
    We use the midpoint ball of half the radius as a lower bound
    for their overlap, rather than introducing its exact invariant volume. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric InnerMidpointParallelogram EuclideanLebesgueDimensions
  EuclideanBallVolume EuclideanClosedBallVolume MetricClosedBalls
  MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [euclidean_midpoint_ball_overlap]: supporting
    lower bound for the overlap used in Federer 3.1.8,
    p. 217. The closed ball at the midpoint with radius
    half the endpoint distance lies in both endpoint balls. *)
Lemma euclidean_midpoint_ball_overlap (R : realType) m
    (u v : inner_metric_space (@euclidean_inner_productP R m)) :
  metric_closed_ball ((2:R)^-1*:(u+v)) (mdist u v/2) `<=`
    (metric_closed_ball u (mdist u v) `&` metric_closed_ball v (mdist u v)).
Proof.
pose N := inner_norm (@euclidean_inner_productP R m).
pose c := (2:R)^-1*:(u+v).
have hu : 2*mdist u c=mdist u v.
  have hh := congr1 N (@inner_midpoint_sum R _ u u v).
  by rewrite /c !inner_metric_distanceE /N inner_normZ normr_nat subrr add0r in hh *.
have hv : 2*mdist v c=mdist u v.
  have hh := congr1 N (@inner_midpoint_sum R _ v u v).
  rewrite /c !inner_metric_distanceE /N inner_normZ normr_nat subrr addr0 in hh *.
  by rewrite -[v-u]opprB inner_normN in hh.
move=> x hx; change (is_true (mdist c x<=mdist u v/2)) in hx.
have htwo : (0<(2 : R)) by rewrite ltr0n.
have hx2 : 2*mdist c x<=mdist u v.
  by move: hx; rewrite ler_pdivlMr // mulrC.
split.
- have hh := metric_triangle u c x; change (is_true (mdist u x<=mdist u v)); lra.
- have hh := metric_triangle v c x; change (is_true (mdist v x<=mdist u v)); lra.
Qed.

(** Source for [euclidean_overlap_mass_coefficient]: a fixed
    positive coefficient for the Q estimates in Federer 3.1.8,
    p. 217. Four times c r^m is the volume of the
    half-radius midpoint ball; this is a supporting proof choice,
    not a redefinition of the book's exact overlap constant rho. *)
Definition euclidean_overlap_mass_coefficient (R : realType) m : R :=
  euclidean_unit_ball_volume R m*((2:R)^-1)^+m/4.

(** Source for [euclidean_overlap_mass_coefficient_positive]:
    positivity needed in the uniform cutoffs in Federer 3.1.8,
    p. 217, from the positive normalized Euclidean ball volume. *)
Lemma euclidean_overlap_mass_coefficient_positive (R : realType) m :
  0<euclidean_overlap_mass_coefficient R m.
Proof.
rewrite /euclidean_overlap_mass_coefficient.
apply: divr_gt0; last by rewrite ltr0n.
apply: mulr_gt0; first exact: (euclidean_unit_ball_volumeE R m).2.
apply: exprn_gt0; by rewrite invr_gt0 ltr0n.
Qed.

(** Source for [euclidean_overlap_good_point]: the choice of x
    outside Q(u,r,j) and Q(v,r,j) in Federer 3.1.8,
    pp. 217–218. Outer-measure bounds suffice, so neither
    exceptional set is assumed measurable. *)
Theorem euclidean_overlap_good_point (R : realType) m
    (A B : set (inner_metric_space (@euclidean_inner_productP R m)))
    (u v : inner_metric_space (@euclidean_inner_productP R m)) :
  u!=v ->
  (euclidean_lebesgue_measure m (A `&` metric_closed_ball u (mdist u v))<=
    (euclidean_overlap_mass_coefficient R m*(mdist u v)^+m)%:E)%E ->
  (euclidean_lebesgue_measure m (B `&` metric_closed_ball v (mdist u v))<=
    (euclidean_overlap_mass_coefficient R m*(mdist u v)^+m)%:E)%E ->
  exists x, metric_closed_ball u (mdist u v) x /\
    metric_closed_ball v (mdist u v) x /\ ~A x /\ ~B x.
Proof.
move=> hne hA hB; apply: contrapT=> hn.
pose r := mdist u v.
pose c := (2:R)^-1*:(u+v).
pose K := metric_closed_ball c (r/2).
have hr : 0<r by rewrite /r mdist_gt0.
have hsub := @euclidean_midpoint_ball_overlap R m u v.
have hcover : K `<=`
    (A `&` metric_closed_ball u r) `|` (B `&` metric_closed_ball v r).
  move=> x hx; have [hxu hxv] := hsub x hx.
  case: (pselect (A x))=> [ha|ha]; first by left; split.
  right; split=> //; apply: contrapT=> hb; apply: hn.
  by exists x; split=> //; split=> //; split.
have hmass := @measure_binary_cover R _ _ (euclidean_lebesgue_is_measure R m)
  K _ _ hcover.
have hb := le_trans hmass (leeD hA hB).
have hr2 : 0<r/2 by rewrite divr_gt0 // ltr0n.
rewrite /K (euclidean_closed_ball_normalized_volume c (ltW hr2)) -EFinD lee_fin in hb.
pose a := euclidean_unit_ball_volume R m*((2:R)^-1)^+m*r^+m.
have ha : 0<a.
  rewrite /a.
  apply: mulr_gt0; last exact: exprn_gt0 hr.
  apply: mulr_gt0; first exact: (euclidean_unit_ball_volumeE R m).2.
  apply: exprn_gt0; by rewrite invr_gt0 ltr0n.
have he1 : euclidean_unit_ball_volume R m*(r/2)^+m=a.
  by rewrite /a exprMn [r^+m * _]mulrC mulrA.
have he2 : euclidean_overlap_mass_coefficient R m*r^+m=a/4.
  by rewrite /a /euclidean_overlap_mass_coefficient mulrAC.
rewrite he1 he2 in hb.
have h4 : (0<(4 : R)) by rewrite ltr0n.
have hh : a/4+a/4<a by nra.
by have := le_lt_trans hb hh; rewrite ltxx.
Qed.
