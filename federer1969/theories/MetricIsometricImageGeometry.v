(** Federer (1969), 3.2.36, p. 273: actual isometric
    images preserve diameter and continuity before convexity is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground LipschitzUP MetricDiameterUP MetricDiameter
  MetricSetDistanceBasic NormMetricScaleContinuity CompactSetDistanceProfile CompactHausdorffMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_isometric_image_diameter]: the exact diameter
    preservation in transporting convex covers for the Q_1 assertion
    of Federer 3.2.36, p. 273. Pairwise distance equality and
    the independent least-upper-bound laws prove equality even for
    empty or unbounded sources; no inverse or chosen image is needed. *)
Lemma metric_isometric_image_diameter (R:realType) (X Y:metricType R) (f:X->Y):
  (forall x y,mdist (f x) (f y)=mdist x y) ->forall A,
    extended_metric_diameter (f @` A)=extended_metric_diameter A.
Proof.
move=>hMetric A.
pose hdA:=extended_metric_diameter_specification A.
pose hdB:=extended_metric_diameter_specification (f @` A).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(metric_diameter_least hdB (metric_diameter_nonnegative hdA)).
  move=>u v [x hx <-] [y hy <-]; rewrite hMetric.
  exact:(@metric_diameter_upper R X A _ hdA x y hx hy).
- apply:(metric_diameter_least hdA (metric_diameter_nonnegative hdB)).
  move=>x y hx hy; rewrite -(hMetric x y).
  apply:(@metric_diameter_upper R Y (f @` A) _ hdB (f x) (f y)).
  + by exists x.
  + by exists y.
Qed.

(** Source for [metric_isometric_map_continuous]: continuity of the
    original metric isometric map used for compact image and closed-cover
    transport in Federer 3.2.36, p. 273. Its proved global
    bound is one, independently of affine classification or dimension. *)
Lemma metric_isometric_map_continuous (R:realType) (X Y:metricType R) (f:X->Y):
  (forall x y,mdist (f x) (f y)=mdist x y) ->continuous f.
Proof.
move=>hMetric; apply:(@metric_fixed_lipschitz_continuous R X Y f 1%R (ler01)).
by move=>x y; rewrite hMetric mul1r.
Qed.

(** Source for [metric_isometric_compact_image_exists]: the compact
    image body used in the isometry assertion of Federer 3.2.36,
    p. 273. Continuity and nonemptiness give a local witness in the
    existing compact Hausdorff carrier, specified by its exact image
    law. No global compact-image operator or private witness is selected. *)
Lemma metric_isometric_compact_image_exists (R:realType) (X Y:metricType R)
    (f:X->Y) (A:compact_hausdorff_space X):
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  exists B:compact_hausdorff_space Y,val B=f @` val A.
Proof.
move=>hMetric.
have hCompact:compact (f @` val A).
  exact:continuous_compact (continuous_subspaceT (metric_isometric_map_continuous hMetric)) (set_valP A).1.
have hNonempty:f @` val A!=set0.
  have [a ha]:=(set_valP A).2; exists (f a); by exists a.
exists (exist _ (f @` val A) (mem_set (conj hCompact hNonempty))); reflexivity.
Qed.
