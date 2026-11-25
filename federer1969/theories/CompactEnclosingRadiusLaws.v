(** Consequences of the least containing-radius laws supporting Federer
    (1969), 2.10.31, pp. 195–196. Uniqueness, comparison and attainment use
    the specification alone. The distance-to-centre maximum is general
    topology on a nonempty compact set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground MetricClosedBalls CompactSetDistanceProfile
  CompactMaximum MetricPairDistance TopologicalProductMaps CompactEnclosingRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_enclosing_radius_unique]: supporting
    uniqueness of the least containing radius used
    in 2.10.31, p. 195. *)
Lemma compact_enclosing_radius_unique (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) (r s : R) :
  is_compact_enclosing_radius a C r -> is_compact_enclosing_radius a C s -> r=s.
Proof.
move=> hr hs; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (enclosing_radius_least_law hr (enclosing_radius_nonnegative_law hs) (enclosing_radius_contains_law hs)).
- exact (enclosing_radius_least_law hs (enclosing_radius_nonnegative_law hr) (enclosing_radius_contains_law hr)).
Qed.

(** Source for [compact_enclosing_radius_monotone]: supporting
    radius comparison under containment for 2.10.31,
    pp. 195–196. It does not require an
    ambient finite-dimensional vector space. *)
Lemma compact_enclosing_radius_monotone (R : realType) (X : metricType R)
    (a : X) (C D : compact_metric_set X) (r s : R) :
  is_compact_enclosing_radius a C r -> is_compact_enclosing_radius a D s ->
  val C `<=` val D -> r<=s.
Proof.
move=> hr hs hCD.
apply: (enclosing_radius_least_law hr (enclosing_radius_nonnegative_law hs))=> x hx.
exact (enclosing_radius_contains_law hs (hCD x hx)).
Qed.

(** Source for [compact_enclosing_radius_attained]: supporting
    attainment of the radial bound in the compact
    minimal-radius argument of 2.10.31, pp. 195–196.
    It also justifies the corrected shrinking-ball
    step on p. 196: the smaller ball has the
    same centre zero, rather than the printed a.
    This is a local proof correction, not an erratum entry. *)
Theorem compact_enclosing_radius_attained (R : realType) (X : metricType R)
    (a : X) (C : compact_metric_set X) (r : R) :
  is_compact_enclosing_radius a C r -> exists x, val C x /\ mdist a x=r.
Proof.
move=> hr.
have hpair : continuous (fun x : X=>(a,x)).
  apply: topological_pair_continuous; first exact: cst_continuous.
  by move=> x.
have hc : continuous (fun x : X=>(mdist a x : real_line_metric R)).
  move=> x; exact (continuous_comp (hpair x) (@metric_pair_distance_continuous R X (a,x))).
have [x [hx hmax]] := continuous_compact_maximum (set_valP C).2 (set_valP C).1 hc.
exists x; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (enclosing_radius_contains_law hr hx).
- apply: (enclosing_radius_least_law hr (mdist_ge0 a x))=> y hy; exact: hmax y hy.
Qed.
