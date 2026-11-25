(** Federer (1969), 2.10.45, printed p. 203, displayed diameter estimate for
    S times T: a cube of side d and a set of diameter at most d have product
    diameter at most sqrt(m+1) d. First prove the abstract squared- diameter
    estimate. It includes empty rectangles, zero diameter and
    zero-dimensional first factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra.
From Federer Require Import ExtendedRealOrderTopology SquaredMetricProductUP SquaredMetricProductLaws
  MetricProductRectangles MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [squared_product_rectangle_diameter_bound]: supporting
    product-diameter estimate in 2.10.45, p. 203.
    Nonnegative finite bounds a and b on the
    factor diameters give every nonnegative r
    with a^2+b^2<=r^2 as a product diameter bound. *)
Lemma squared_product_rectangle_diameter_bound (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_squared_metric_product pair first second)
    (U : set X) (V : set Y) (a b r : R) :
  0<=a -> 0<=b -> 0<=r -> a^+2+b^+2<=r^+2 ->
  (extended_metric_diameter U<=a%:E)%E -> (extended_metric_diameter V<=b%:E)%E ->
    (extended_metric_diameter (metric_product_rectangle first second U V)<=r%:E)%E.
Proof.
move=> ha hb hr hs hU hV.
apply: (metric_diameter_least (extended_metric_diameter_specification _)).
- by rewrite lee_fin.
- move=> p q [hpU hpV] [hqU hqV]; rewrite lee_fin.
  have hfirst : mdist (first p) (first q)<=a.
    have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification U) hpU hqU) hU.
    by rewrite lee_fin in hh.
  have hsecond : mdist (second p) (second q)<=b.
    have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification V) hpV hqV) hV.
    by rewrite lee_fin in hh.
  rewrite -(ler_sqr (mdist_ge0 _ _) hr) (squared_metric_product_distance_coordinates hp).
  have hs1 : mdist (first p) (first q)^+2<=a^+2.
    by rewrite (ler_sqr (mdist_ge0 _ _) ha).
  have hs2 : mdist (second p) (second q)^+2<=b^+2.
    by rewrite (ler_sqr (mdist_ge0 _ _) hb).
  exact: le_trans (lerD hs1 hs2) hs.
Qed.

(** Source for [squared_product_cube_diameter_bound]: direct
    sqrt(m+1) d product bound in 2.10.45,
    p. 203, once the first cube's diameter
    bound sqrt(m) d is supplied. The statement
    also includes d=0 and m=0. *)
Lemma squared_product_cube_diameter_bound (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_squared_metric_product pair first second)
    (U : set X) (V : set Y) m (d : R) :
  0<=d -> (extended_metric_diameter U<=(Num.sqrt m%:R*d)%:E)%E ->
    (extended_metric_diameter V<=d%:E)%E ->
    (extended_metric_diameter (metric_product_rectangle first second U V)<=(Num.sqrt m.+1%:R*d)%:E)%E.
Proof.
move=> hd hU hV.
have hm : (0<=m%:R :> R) by exact: ler0n.
have hsucc : (m.+1%:R : R)=m%:R+1 by rewrite -[m.+1]addn1 natrD.
have hm1 : (0<=m.+1%:R :> R) by exact: ler0n.
apply: (@squared_product_rectangle_diameter_bound R P X Y pair first second hp U V
  (Num.sqrt m%:R*d) d (Num.sqrt m.+1%:R*d))=> //.
- exact: mulr_ge0 (sqrtr_ge0 _) hd.
- exact: mulr_ge0 (sqrtr_ge0 _) hd.
- rewrite !exprMn !sqr_sqrtr // hsucc; nra.
Qed.
