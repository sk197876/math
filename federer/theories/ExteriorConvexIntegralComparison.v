(** Federer (1969), 2.10.37, printed p. 198: T^m(A)<=alpha(m) 2^(-m) m!
    Q_t^m(A), for arbitrary A and 1<=t<=infinity. Combine the proved
    endpoint-norm comparison and covering laws on the original open convex
    generators. These generators are Borel and hence Suslin, which justifies
    the intermediate norm measurability without imposing a hypothesis on A.
    All measures, norms and projection constants are the previously
    specified sealed objects. No correction on p. 198 occurs in the working
    Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBallVolume HausdorffDiameterCost
  ExteriorMeasureUP ExteriorMeasure ExteriorMeasureGauge ProjectionMeasureUP
  IntegralGeometricMeasureUP IntegralGeometricMeasure IntegralGeometricGauge
  ExteriorIntegralGaugeBound ExteriorMeasureWeightedComparison TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [exterior_convex_integral_geometric_bound]: direct
    corollary 2.10.37, p. 198, expressed
    through the existing alpha(m)/2^m coefficient.
    The degree and projection dimension hypotheses
    retain the positive m<=n convention of
    the Q_t definition in 2.10.5, p. 173. *)
Theorem exterior_convex_integral_geometric_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  (0<m)%N -> (1<=t)%E -> forall A,
  (@exterior_diameter_measure R n m A <=
    ((hausdorff_normalisation R m)*(m`!)%:R)%:E*
      @convex_integral_geometric_measure R n m hmn t A)%E.
Proof.
move=> hm ht A.
apply: (@exterior_measure_weighted_generator_comparison R n m (open_convex_euclidean_sets R n)
  (fun j=>val j) (fun j=>@integral_geometric_gauge R n m hmn t (val j)) _ _
  ((hausdorff_normalisation R m)*(m`!)%:R)
  (exterior_diameter_measure_specification R n m)
  (@convex_integral_geometric_measure_specification R n m hmn t) _ _ _ A).
- move=> j; apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)).
  exact: metric_borel_suslin (open_borel_set (set_valP j).1).
- apply: mulr_gt0; first exact: hausdorff_normalisation_positive.
  by rewrite ltr0n fact_gt0.
- move=> j; apply: (@convex_exterior_cost_integral_gauge_bound R n m hmn t (val j)
    hm ht (set_valP j).2).
  exact: metric_borel_suslin (open_borel_set (set_valP j).1).
Qed.

(** Source for [federer_2_10_37]: direct numbered
    corollary 2.10.37, printed p. 198.
    In words, exterior-diameter measure is at most
    alpha(m) 2^(-m) m! times Q_t^m on
    every target set. The coefficient uses the
    actual Euclidean unit-ball volume alpha(m),
    and every exponent through infinity is included. *)
Theorem federer_2_10_37 (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  (0<m)%N -> (1<=t)%E -> forall A,
  (@exterior_diameter_measure R n m A <=
    ((euclidean_unit_ball_volume R m/(2 : R)^+m)*(m`!)%:R)%:E*
      @convex_integral_geometric_measure R n m hmn t A)%E.
Proof. exact: exterior_convex_integral_geometric_bound. Qed.
