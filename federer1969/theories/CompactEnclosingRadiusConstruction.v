(** Private enclosing-radius existence proof supporting Federer (1969),
    2.10.31, p. 195. A continuous distance-to-centre function attains its
    maximum on a nonempty compact set. That value satisfies the
    independently stated least containing-radius laws; no choice of
    maximizing point is exposed downstream. Source context:
    CompactEnclosingRadiusUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactSetDistanceProfile
  CompactMaximum MetricPairDistance TopologicalProductMaps CompactEnclosingRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_enclosing_radius_exists]: supporting
    existence of the scalar radius minimised over
    the compact-set class in 2.10.31, p. 195.
    This construction only proves the abstract laws. *)
Theorem compact_enclosing_radius_exists (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) :
  exists r : R, is_compact_enclosing_radius a C r.
Proof.
have hpair : continuous (fun x : X=>(a,x)).
  apply: topological_pair_continuous; first exact: cst_continuous.
  by move=> x.
have hc : continuous (fun x : X=>(mdist a x : real_line_metric R)).
  move=> x; exact (continuous_comp (hpair x) (@metric_pair_distance_continuous R X (a,x))).
have [x [hx hmax]] := continuous_compact_maximum (set_valP C).2 (set_valP C).1 hc.
exists (mdist a x); constructor.
- exact: mdist_ge0.
- move=> y hy; exact (hmax y hy).
- move=> s hs hbound; exact (hbound x hx).
Qed.
