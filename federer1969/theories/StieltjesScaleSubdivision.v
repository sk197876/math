(** Federer (1969), 2.10.7, p. 174, proof paragraph: all positive
    size-cutoff approximating measures are equal. First extend the small
    interval generator bound to every bounded open interval by subdividing
    at continuity points and discarding their null atoms. Then compare the
    two actual covering infima by the measure covering inequality. We retain
    Federer's raw cost. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP StieltjesIntervalBounds
  StieltjesScalePointNull MonotoneIntervalSubdivision StieltjesMonotone CurveDiscontinuities
  RealMetricCompleteness
  MetricScaleEnvelopeUP MetricScaleCutoffCost MetricScaleMeasureBound
  CaratheodoryBorelRegular CaratheodoryLimitUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [stieltjes_scale_all_interval_bound]:
    supporting raw-increment bound after fine
    subdivision in Federer 2.10.7, p. 174.
    The original interval endpoints need not
    be continuity points of g. *)
Theorem stieltjes_scale_all_interval_bound (R : realType) (g : R -> R)
    (delta : \bar R) (nu : set (real_line_metric R) -> \bar R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) ->
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta nu ->
  0<delta -> forall a b, (a<b)%R -> nu `]a,b[<=(g b-g a)%:E.
Proof.
move=> hg hnu hdelta.
have hfin := @monotone_locally_finite_variation R g hg.
pose Y := [the metricType R of real_line_metric R].
pose C := @curve_jump_points R Y g.
have hC : countable C := @curve_jump_points_countable R Y g hfin.
have hcont x : ~ C x -> g @ x --> g x.
  move=> hx; apply: contrapT=> hn; apply: hx.
  exact ((@curve_jump_points_iff R Y g hfin (@real_line_metric_complete R) x).2 hn).
have [k hk] := reciprocal_metric_cutoffs_cofinal hdelta.
pose d : R := (((k.+1)%:R)^-1)%R.
have hd : (0<d)%R by rewrite /d invr_gt0 ltr0n.
have hm := metric_scale_envelope_is_measure hnu (stieltjes_interval_cost_nonnegative hg).
apply: (@interval_increment_subdivision_bound R g nu hm C d hC hd).
- move=> x hx; exact: (@stieltjes_scale_continuity_point_null R g delta nu x
    hg hnu hdelta (hcont x hx)).
- move=> a b hab hsmall.
  apply: (@stieltjes_scale_small_interval_bound R g delta nu a b hg hnu hab).
  apply: le_trans _ hk; rewrite lee_fin; exact: ltW hsmall.
Qed.

(** Source for [stieltjes_positive_scales_agree]: direct
    equality of all positive-cutoff approximation
    measures in Federer 2.10.7, p. 174.
    Cutoffs can be finite or infinite; target
    sets are arbitrary. Both approximations
    satisfy their independent infimum laws. *)
Theorem stieltjes_positive_scales_agree (R : realType) (g : R -> R)
    (delta eta : \bar R) (nu xi : set (real_line_metric R) -> \bar R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) -> 0<delta -> 0<eta ->
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta nu ->
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) eta xi ->
  forall A, nu A=xi A.
Proof.
move=> hg hd he hnu hxi A.
have hdir (d e : \bar R) (u v : set (real_line_metric R) -> \bar R)
    (hu : is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) d u)
    (hv : is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) e v) :
    0<d -> u A<=v A.
  move=> hd'.
  apply: (@measure_bounded_by_metric_scale_envelope R [the metricType R of real_line_metric R]
    (stieltjes_open_intervals R) (@stieltjes_interval_set R) (stieltjes_interval_cost g) e v u hv
    (metric_scale_envelope_is_measure hu (stieltjes_interval_cost_nonnegative hg)))=> j _.
  exact: (@stieltjes_scale_all_interval_bound R g d u hg hu hd' (val j).1 (val j).2 (set_valP j)).
apply/eqP; rewrite eq_le (hdir delta eta nu xi hnu hxi hd) (hdir eta delta xi nu hxi hnu he).
by [].
Qed.

(** Source for [stieltjes_limit_equals_every_scale]:
    supporting equality of the final interval
    measure with every positive size approximation
    in Federer 2.10.7, p. 174. Use only
    the abstract infimum and supremum laws. *)
Theorem stieltjes_limit_equals_every_scale (R : realType) (g : R -> R)
    (mu nu : set (real_line_metric R) -> \bar R) (delta : \bar R) :
  (forall x y, (x<=y)%R -> (g x<=g y)%R) ->
  is_stieltjes_caratheodory_measure g mu -> 0<delta ->
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta nu ->
  forall A, mu A=nu A.
Proof.
move=> hg hmu hd hnu A.
have hlower := @caratheodory_limit_upper R [the metricType R of real_line_metric R]
  (stieltjes_open_intervals R) (@stieltjes_interval_set R) (stieltjes_interval_cost g)
  mu hmu A delta nu hd hnu.
apply/eqP; rewrite eq_le hlower andbT.
apply: (caratheodory_limit_least hmu)=> eta xi he hxi.
by rewrite (@stieltjes_positive_scales_agree R g eta delta xi nu hg he hd hxi hnu A).
Qed.
