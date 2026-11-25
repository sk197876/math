(** Federer (1969), 2.10.45, printed pp. 202–203: coordinate maps of the
    squared-distance product are nonexpanding and each fixed-coordinate
    slice is isometric to its factor. Derive these supporting facts from the
    abstract product laws before the rectangle-covering estimates. No
    implementation of the product metric is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import LipschitzUP MetricCartesianProductUP SquaredMetricProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [squared_metric_product_distance_coordinates]: supporting
    squared-distance formula for arbitrary product
    points in the hypothesis of 2.10.45,
    p. 202, obtained by coordinate recovery. *)
Lemma squared_metric_product_distance_coordinates (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_squared_metric_product pair first second) p q :
  mdist p q^+2=mdist (first p) (first q)^+2+mdist (second p) (second q)^+2.
Proof.
have hh := squared_product_distance_law hp (first p) (second p) (first q) (second q).
by rewrite !(squared_product_recovery_law hp) in hh.
Qed.

(** Source for [squared_metric_product_cartesian]: supporting
    projection bounds needed to apply 2.10.27,
    pp. 190–191, in the proof of 2.10.45,
    p. 202. Both bounds follow from the
    squared-distance equality; they are not assumed. *)
Theorem squared_metric_product_cartesian (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second :
  is_squared_metric_product pair first second -> is_metric_cartesian_product pair first second.
Proof.
move=> hp; constructor.
- exact: squared_product_first_pair_law hp.
- exact: squared_product_second_pair_law hp.
- exact: squared_product_recovery_law hp.
- split; first exact: ler01.
  move=> p q _ _; rewrite mul1r -(ler_sqr (mdist_ge0 _ _) (mdist_ge0 _ _))
    (squared_metric_product_distance_coordinates hp).
  have hh := sqr_ge0 (mdist (second p) (second q)); nra.
- split; first exact: ler01.
  move=> p q _ _; rewrite mul1r -(ler_sqr (mdist_ge0 _ _) (mdist_ge0 _ _))
    (squared_metric_product_distance_coordinates hp).
  have hh := sqr_ge0 (mdist (first p) (first q)); nra.
Qed.

(** Source for [squared_metric_product_first_slice]: supporting
    isometry of a fixed second-coordinate slice
    in 2.10.45, p. 202, from the
    actual squared-distance hypothesis. *)
Lemma squared_metric_product_first_slice (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_squared_metric_product pair first second) y x u :
  mdist (pair x y) (pair u y)=mdist x u.
Proof.
have he := squared_product_distance_law hp x y u y.
rewrite mdistxx expr0n addr0 in he.
have h1 := mdist_ge0 (pair x y) (pair u y).
have h2 := mdist_ge0 x u; nra.
Qed.

(** Source for [squared_metric_product_second_slice]: supporting
    isometry of a fixed first-coordinate slice
    in 2.10.45, p. 202, with no
    nonempty or positive-dimensional factor hypothesis. *)
Lemma squared_metric_product_second_slice (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_squared_metric_product pair first second) x y v :
  mdist (pair x y) (pair x v)=mdist y v.
Proof.
have he := squared_product_distance_law hp x y x v.
rewrite mdistxx expr0n add0r in he.
have h1 := mdist_ge0 (pair x y) (pair x v).
have h2 := mdist_ge0 y v; nra.
Qed.
