(** Federer (1969), 2.10.29, p. 194: a set of diameter d in the real plane
    lies in a rectangle U times V with both interval lengths equal to d. The
    product measure is bounded by the product of the interval masses.
    Supporting lemmas allow any abstract Cartesian metric with nonexpanding
    projections, as in 2.10.27, p. 190. The measure uses only the existing
    sealed product and image-measure interfaces, not a new measure
    construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameterUP MetricDiameter MetricDiameterReal CompactIntervalGauge
  MetricCartesianProductUP LipschitzUP MeasureUP MeasureBasic MeasureSplit MeasurePushforward ProductMeasure ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [paired_product_measure]: supporting expression
    of the Cartesian product measure on the ambient
    product carrier in 2.10.29, p. 194.
    Pairing pushes forward the already specified
    product measure; its implementation stays opaque. *)
Definition paired_product_measure (R : realType) (P X Y : choiceType)
    (pair : X -> Y -> P) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :=
  measure_pushforward (fun p : X*Y=>pair p.1 p.2) (product_measure ha hb).

(** Source for [paired_product_is_measure]: supporting measure
    law for the product used in 2.10.29,
    p. 194, by 2.6.1, p. 115, and
    the image measure definition of 2.1.2, p. 54. *)
Lemma paired_product_is_measure (R : realType) (P X Y : choiceType)
    (pair : X -> Y -> P) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_measure (paired_product_measure pair ha hb).
Proof. exact: measure_pushforward_is_measure (product_measure_is_measure ha hb). Qed.

(** Source for [paired_product_rectangle_bound]: supporting
    rectangle bound used in both cases of 2.10.29,
    p. 194. The covering set need not be
    measurable; only the two rectangle factors are. *)
Lemma paired_product_rectangle_bound (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) (first : P -> X) (second : P -> Y)
    (hp : is_metric_cartesian_product pair first second)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set P) (U : set X) (V : set Y) :
  measure_measurable alpha U -> measure_measurable beta V ->
  (forall p, S p -> U (first p) /\ V (second p)) ->
  paired_product_measure pair ha hb S<=alpha U*beta V.
Proof.
move=> hU hV hsub.
have hcover : ((fun p : X*Y=>pair p.1 p.2) @^-1` S) `<=` (U `*` V).
  move=> [x y] hxy.
  have hh := hsub (pair x y) hxy.
  by rewrite (metric_product_first_pair hp) (metric_product_second_pair hp) in hh.
exact (le_trans (measure_mono (product_measure_is_measure ha hb) hcover)
  (product_measure_rectangle_bound ha hb hU hV)).
Qed.

(** Source for [paired_product_coordinate_rectangle_value]: supporting
    exact positive mass of the Cantor product
    in 2.10.29, p. 194. Coordinate rectangle
    membership pulls back exactly to the factor
    rectangle by the abstract pairing laws. *)
Lemma paired_product_coordinate_rectangle_value (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) (first : P -> X) (second : P -> Y)
    (hp : is_metric_cartesian_product pair first second)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  paired_product_measure pair ha hb [set p | A (first p) /\ B (second p)]=alpha A*beta B.
Proof.
move=> hA hB.
have he : ((fun p : X*Y=>pair p.1 p.2) @^-1` [set p | A (first p) /\ B (second p)])=A `*` B.
  apply/seteqP; split=> p; rewrite /= (metric_product_first_pair hp) (metric_product_second_pair hp); by [].
rewrite /paired_product_measure /measure_pushforward he.
exact (@product_measure_rectangle_value R X Y alpha beta ha hb A B hA hB).
Qed.

(** Source for [paired_product_whole_value]: supporting
    positive total product mass in 2.10.29,
    p. 194; no finiteness or sigma-finiteness
    is needed for this rectangle identity. *)
Lemma paired_product_whole_value (R : realType) (P X Y : choiceType)
    (pair : X -> Y -> P) (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  paired_product_measure pair ha hb setT=alpha setT*beta setT.
Proof.
rewrite /paired_product_measure /measure_pushforward preimage_setT.
have he : (setT : set (X*Y))=setT `*` setT by apply/seteqP; split=> p _; by [].
rewrite he; exact (product_measure_rectangle_value ha hb (measure_measurable_whole ha) (measure_measurable_whole hb)).
Qed.

(** Source for [metric_cartesian_real_rectangle_hull]: direct
    same-length interval rectangle in 2.10.29,
    p. 194, proved from nonexpanding projections.
    Degenerate intervals are included, and no
    projection extremum is assumed attained. *)
Theorem metric_cartesian_real_rectangle_hull (R : realType) (P : metricType R)
    (pair : real_line_metric R -> real_line_metric R -> P)
    (first second : P -> real_line_metric R)
    (hp : is_metric_cartesian_product pair first second) (S : set P) (d : R) :
  S !=set0 -> (0<=d)%R -> extended_metric_diameter S<=d%:E ->
  exists U V : compact_real_intervals R,
    @extended_metric_diameter R [the metricType R of real_line_metric R] (val U)=d%:E /\
    @extended_metric_diameter R [the metricType R of real_line_metric R] (val V)=d%:E /\
    forall p, S p -> val U (first p) /\ val V (second p).
Proof.
move=> hS hd hdiam.
have hh (g : P -> real_line_metric R)
    (hg : is_metric_lipschitz_bound setT g 1%R) :
    exists T : compact_real_intervals R,
      @extended_metric_diameter R [the metricType R of real_line_metric R] (val T)=d%:E /\
      forall p, S p -> val T (g p).
  have himage : g @` S !=set0.
    have [p hpS] := hS; exists (g p); by exists p.
  have hdist x y : (g @` S) x -> (g @` S) y -> (`|x-y|<=d)%R.
    move=> [p hpS <-] [q hqS <-].
    have hproj := hg.2 p q Logic.I Logic.I.
    rewrite mul1r real_line_metric_distanceE in hproj.
    have hpq := le_trans (metric_diameter_upper (extended_metric_diameter_specification S) hpS hqS) hdiam.
    rewrite lee_fin in hpq; exact: le_trans hproj hpq.
  have hhull := @real_bounded_diameter_interval_hull R (g @` S) d himage hdist.
  have hord : (inf (g @` S)<=inf (g @` S)+d)%R by rewrite lerDl.
  have hI : is_compact_real_interval (`[inf (g @` S),(inf (g @` S)+d)%R] : set (real_line_metric R)).
    exists (inf (g @` S)),(inf (g @` S)+d)%R; by split.
  pose T : compact_real_intervals R := Sub (`[inf (g @` S),(inf (g @` S)+d)%R] : set (real_line_metric R)) (mem_set hI).
  exists T; split.
  - by rewrite /T /= (extended_metric_diameter_segment hord) addrAC subrr add0r.
  - move=> p hpS; apply: hhull; by exists p.
have [U [hU hfirst]] := hh first (metric_product_first_nonexpanding hp).
have [V [hV hsecond]] := hh second (metric_product_second_nonexpanding hp).
exists U,V; split=> //; split=> //; move=> p hpS; split; [exact: hfirst hpS | exact: hsecond hpS].
Qed.
