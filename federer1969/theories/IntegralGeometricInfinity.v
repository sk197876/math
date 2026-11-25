(** Federer (1969), 2.10.5(2), p. 173, infinity-exponent identity,
    paraphrased: Q_infinity^m equals Caratheodory measure C^m. The actual
    theta* has positive mass on every nonempty open parameter set. For open
    S, the proved open strict superlevels of f_S identify its essential
    supremum with its supremum. Thus the two independently constructed
    measures have the same generator costs. This supporting gauge identity
    holds even for unbounded, nonconvex open S; the measure families retain
    the book's convex generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric ProjectedVolumeMeasurability ProjectedVolumeLowerContinuity
  ProjectedVolumeGauge ProjectionMeasureUP ProjectionMeasure
  OrthogonalProjectionProbability NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm
  NonnegativeExtendedEssentialBounds ProjectionProbabilitySupport ExtendedRealBoundsUP
  IntegralGeometricGauge IntegralGeometricMeasureUP IntegralGeometricMeasure ProjectionBeta
  BorelClosedProjection TopologicalBorel CaratheodoryLimitUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_infinity_open]:
    supporting equality of the infinity and
    supremum gauges for the identity in Federer
    2.10.5(2), p. 173. The proof uses
    open superlevels and full support of the
    actual theta*, retaining infinite volumes. *)
Theorem integral_geometric_gauge_infinity_open (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  open S -> @integral_geometric_gauge R n m hmn +oo S=projected_volume_gauge m S.
Proof.
move=> hS.
pose P := euclidean_projection_space R n m.
pose f : P -> _ := projected_volume_function (m:=m) S.
pose theta := @orthogonal_projection_probability R n m hmn.
pose a := nonnegative_extended_exponent_norm theta f +oo.
have hsus := @metric_borel_suslin R (inner_metric_space (@euclidean_inner_productP R n))
  S (open_borel_set hS).
have hn := @nonnegative_extended_exponent_norm_specification R _ theta f +oo
  (@theta_star_is_measure R n m hmn) (fun p => projected_volume_function_nonnegative S p)
  (leey 1) (@theta_star_projected_volume_measurable R n m hmn S hsus).
have [p hp] := @euclidean_projection_exists R n m hmn.
have [q hq] := @euclidean_projection_linear_complete R n m p hp.
have hsup := @nonnegative_extended_essential_supremum R P theta
  (@theta_star_is_measure R n m hmn) f a (ex_intro _ q I)
  (fun p => projected_volume_function_nonnegative S p)
  (fun b => @projected_volume_open_superlevel R n m S b hS)
  (fun U => @theta_star_nonempty_open_positive R n m hmn U) hn.
rewrite /integral_geometric_gauge projection_beta_infinity invr1 mul1e.
change (a=projected_volume_gauge m S).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (extended_real_supremum_least hsup)=> b [r _ <-].
  exact: (@projected_volume_gauge_projection_bound R n m S (euclidean_projection_linear r)
    (euclidean_projection_linear_member r)).
- apply: projected_volume_gauge_least_bound=> r hr.
  have [s hs] := @euclidean_projection_linear_complete R n m r hr.
  have he : euclidean_projection_linear s @` S=r @` S.
    apply/seteqP; split=> y.
    - move=> [x hx <-]; exists x=> //; exact: esym (hs x).
    - move=> [x hx <-]; exists x=> //; exact: hs x.
  have hh : f s<=a by apply: (extended_real_supremum_upper hsup); by exists s.
  by rewrite /f /projected_volume_function he in hh.
Qed.

(** Source for [convex_integral_geometric_infinity]:
    direct Q_infinity^m=C^m in Federer 2.10.5(2),
    p. 173. Both measures were independently
    selected from their abstract covering laws;
    equality follows from the proved cost identity
    on every open convex generator. *)
Theorem convex_integral_geometric_infinity (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  @convex_integral_geometric_measure R n m hmn +oo A = @caratheodory_projection_measure R n m A.
Proof.
have he : (fun j : open_convex_euclidean_sets R n =>
    @integral_geometric_gauge R n m hmn +oo (val j)) =
    (fun j : open_convex_euclidean_sets R n => projected_volume_gauge m (val j)).
  apply: funext=> j.
  exact: (@integral_geometric_gauge_infinity_open R n m hmn (val j) (set_valP j).1).
have hq := @convex_integral_geometric_measure_specification R n m hmn +oo.
rewrite /is_convex_integral_geometric_measure he in hq.
exact: (caratheodory_limit_unique hq (@caratheodory_projection_measure_specification R n m) A).
Qed.
