(** Federer (1969), 2.2.10, p. 66: the closed set A={(x,t): t dist(x,X minus
    S)=1} projects bijectively onto a proper open set S. The narrow
    normed_module import supplies continuity of real multiplication as
    scalar-topology background; the projection argument is proved here.
    Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology normed_module.
From Federer Require Import RealMetricBackground TopologicalProductMaps
  MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceClosure
  MetricSetDistanceContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distance_reciprocal_graph]: direct definition of the closed
    real-coordinate witness A in Federer 2.2.10, p. 66. *)
Definition distance_reciprocal_graph (R : realType) (T : metricType R)
    (d : T -> R) : set (T * real_line_metric R) :=
  [set p | p.2 * d p.1 = 1].

(** Source for [distance_reciprocal_graph_closed]: direct closedness
    assertion for A in Federer 2.2.10, p. 66: it is the
    inverse image of the closed singleton {1} under the continuous
    product of the real coordinate and distance to the complement. *)
Lemma distance_reciprocal_graph_closed (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) :
  closed (distance_reciprocal_graph d).
Proof.
pose f (p : T * real_line_metric R) : real_line_metric R := p.2 * d p.1.
have hf : continuous f.
  move=> p; apply: cvgM.
  - exact: second_projection_continuous.
  - exact: continuous_comp (@first_projection_continuous T (real_line_metric R) p)
      (@metric_set_distance_continuous R T A d hd p.1).
have h1 : closed [set (1 : real_line_metric R)].
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
exact: (proj1 (continuous_closedP f) hf _ h1).
Qed.

(** Source for [distance_reciprocal_graph_image]: direct projection
    assertion for A in Federer 2.2.10, p. 66. On S the
    complement distance is positive and its reciprocal supplies t;
    outside S the distance vanishes, so the equation is impossible. *)
Lemma distance_reciprocal_graph_image (R : realType) (T : metricType R)
    (S : set T) d (hd : is_metric_set_distance (~` S) d) :
  open S -> (@fst T (real_line_metric R)) @` distance_reciprocal_graph d = S.
Proof.
move=> hS; apply/seteqP; split.
- move=> x [[y t] ht <-]; apply: contrapT=> hy.
  have hz := @metric_set_distance_member R T (~` S) d hd y hy.
  change (t * d y = 1) in ht.
  by move: ht; rewrite hz mulr0; move/eqP; rewrite eq_sym oner_eq0.
- move=> x hx; have hp : 0 < d x.
    apply: (@metric_set_distance_positive_outside_closed R T (~` S) d hd x).
    + exact: open_closedC hS.
    + by move=> hn; exact: hn hx.
  exists (x, (d x)^-1)=> //.
  change ((d x)^-1 * d x = 1); by rewrite mulVf // gt_eqF.
Qed.

(** Source for [distance_reciprocal_graph_injective]: direct
    univalence assertion for p restricted to A in Federer
    2.2.10, p. 66. The equation determines t uniquely,
    because a distance satisfying t*d(x)=1 cannot be zero. *)
Lemma distance_reciprocal_graph_injective (R : realType) (T : metricType R)
    (d : T -> R) (p q : T * real_line_metric R) :
  distance_reciprocal_graph d p -> distance_reciprocal_graph d q ->
  p.1 = q.1 -> p = q.
Proof.
case: p=> x t; case: q=> y u; rewrite /distance_reciprocal_graph /=.
move=> ht hu hxy; subst y.
have hn : d x != 0.
  apply/negP=> /eqP hz; by move: ht; rewrite hz mulr0; move/eqP; rewrite eq_sym oner_eq0.
have he : t = u by apply: (mulIf hn); rewrite ht hu.
by rewrite he.
Qed.
