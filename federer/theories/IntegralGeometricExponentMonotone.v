(** Federer (1969), 2.10.5, p. 173, paragraph following the Gillespie name,
    paraphrased: for every A, beta_t(n,m)I_t^m(A) and beta_t(n,m)Q_t^m(A)
    are nondecreasing in t. Compare the actual norm numerators on all Suslin
    generators, including unbounded ones, using the probability assertion of
    2.4.17, p. 90. The proved weighted Caratheodory comparison passes that
    inequality to the independently constructed measures. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric SuslinSetUP BorelClosedProjection
  IntegralGeometricGauge IntegralGeometricMeasureUP IntegralGeometricMeasure
  ProjectionMeasureUP ProjectionBeta OrthogonalProjectionProbability ProjectedVolumeMeasurability
  ProbabilityNonnegativeExtendedNorm CaratheodoryLimitUP CaratheodoryWeightedComparison
  BorelCoverCostUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_normalized_gauge_monotone]:
    supporting comparison of the actual normalized
    costs for the measure monotonicity in Federer
    2.10.5, p. 173. Every Suslin source is
    allowed; no boundedness hypothesis is added. *)
Theorem integral_geometric_normalized_gauge_monotone (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (s t : \bar R) :
  is_suslin_set R S -> 1<=s -> s<=t ->
  (@projection_beta R n m hmn s)%:E * @integral_geometric_gauge R n m hmn s S <=
  (@projection_beta R n m hmn t)%:E * @integral_geometric_gauge R n m hmn t S.
Proof.
move=> hS hs hst; have ht := le_trans hs hst.
rewrite (@integral_geometric_gauge_normalized R n m hmn s hs S)
  (@integral_geometric_gauge_normalized R n m hmn t ht S).
exact: (@probability_nonnegative_extended_norm_monotone R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_function (m:=m) S) s t (@theta_star_total R n m hmn)
  (fun p => projected_volume_function_nonnegative S p) hs hst
  (@theta_star_projected_volume_measurable R n m hmn S hS)).
Qed.

(** Source for [integral_geometric_normalized_family_monotone]:
    supporting common covering argument for I_t
    and Q_t in Federer 2.10.5, p. 173.
    All generators are Suslin; the target set
    is arbitrary and need not be measurable or
    have finite measure. *)
Lemma integral_geometric_normalized_family_monotone (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (J : choiceType)
    (S : J -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (s t : \bar R) :
  (forall j, is_suslin_set R (S j)) -> 1<=s -> s<=t ->
  is_caratheodory_limit S (fun j => @integral_geometric_gauge R n m hmn s (S j)) mu ->
  is_caratheodory_limit S (fun j => @integral_geometric_gauge R n m hmn t (S j)) nu ->
  forall A, (@projection_beta R n m hmn s)%:E*mu A<=(@projection_beta R n m hmn t)%:E*nu A.
Proof.
move=> hS hs hst hm hn A; have ht := le_trans hs hst.
exact: (@caratheodory_normalized_cost_comparison R
  (inner_metric_space (@euclidean_inner_productP R n)) J S
  (fun j => @integral_geometric_gauge R n m hmn s (S j))
  (fun j => @integral_geometric_gauge R n m hmn t (S j)) mu nu
  (@projection_beta R n m hmn s) (@projection_beta R n m hmn t) hm hn
  (fun j => @integral_geometric_gauge_nonnegative R n m hmn s hs (S j) (hS j))
  (fun j => @integral_geometric_gauge_nonnegative R n m hmn t ht (S j) (hS j))
  (@projection_beta_positive R n m hmn s hs) (@projection_beta_positive R n m hmn t ht)
  (fun j => @integral_geometric_normalized_gauge_monotone R n m hmn (S j) s t (hS j) hs hst) A).
Qed.

(** Source for [integral_geometric_normalized_measure_monotone]:
    direct beta_t I_t^m(A) monotonicity in
    Federer 2.10.5, p. 173. The target
    A is arbitrary; infinite measure values
    and the infinity exponent are included. *)
Theorem integral_geometric_normalized_measure_monotone (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (s t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=s -> s<=t ->
  (@projection_beta R n m hmn s)%:E * @integral_geometric_measure R n m hmn s A <=
  (@projection_beta R n m hmn t)%:E * @integral_geometric_measure R n m hmn t A.
Proof.
move=> hs hst.
apply: (@integral_geometric_normalized_family_monotone R n m hmn
  (@borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (@integral_geometric_measure R n m hmn s)
  (@integral_geometric_measure R n m hmn t) s t _ hs hst
  (@integral_geometric_measure_specification R n m hmn s)
  (@integral_geometric_measure_specification R n m hmn t) A)=> j.
exact: metric_borel_suslin (set_valP j).
Qed.

(** Source for [convex_integral_geometric_normalized_measure_monotone]:
    direct beta_t Q_t^m(A) monotonicity in
    Federer 2.10.5, p. 173. Open convex
    generators are Borel, hence Suslin; no
    boundedness or finiteness premise is added. *)
Theorem convex_integral_geometric_normalized_measure_monotone (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (s t : \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  1<=s -> s<=t ->
  (@projection_beta R n m hmn s)%:E * @convex_integral_geometric_measure R n m hmn s A <=
  (@projection_beta R n m hmn t)%:E * @convex_integral_geometric_measure R n m hmn t A.
Proof.
move=> hs hst.
apply: (@integral_geometric_normalized_family_monotone R n m hmn
  (open_convex_euclidean_sets R n) (fun j => val j)
  (@convex_integral_geometric_measure R n m hmn s)
  (@convex_integral_geometric_measure R n m hmn t) s t _ hs hst
  (@convex_integral_geometric_measure_specification R n m hmn s)
  (@convex_integral_geometric_measure_specification R n m hmn t) A)=> j.
apply: metric_borel_suslin; exact: open_borel_set (set_valP j).1.
Qed.
