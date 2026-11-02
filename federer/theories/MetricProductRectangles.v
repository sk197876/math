(** Federer (1969), 2.10.45, printed pp. 202–203: U times V in the abstract
    Cartesian metric product. Membership is determined by the two
    projections; this is a derived set expression, not a choice of a new
    carrier or metric. The image characterisation follows from the pairing
    and recovery laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricCartesianProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_product_rectangle]: direct product
    set U times V in 2.10.45, p. 202,
    on the supplied abstract product carrier. *)
Definition metric_product_rectangle (P X Y : Type) (first : P -> X) (second : P -> Y)
    (U : set X) (V : set Y) : set P := first @^-1` U `&` second @^-1` V.

(** Source for [metric_product_rectangle_pair]: supporting
    paired-point membership in U times V of
    2.10.45, p. 202. *)
Lemma metric_product_rectangle_pair (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_metric_cartesian_product pair first second) U V x y :
  metric_product_rectangle first second U V (pair x y) <-> U x /\ V y.
Proof.
by rewrite /metric_product_rectangle /= (metric_product_first_pair hp) (metric_product_second_pair hp).
Qed.

(** Source for [metric_product_rectangle_image]: supporting
    identification of the coordinate-defined product
    with the image of U times V in
    2.10.45, p. 202. No factor is
    required to be inhabited or measurable. *)
Lemma metric_product_rectangle_image (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_metric_cartesian_product pair first second) U V :
  metric_product_rectangle first second U V=(fun q : X*Y=>pair q.1 q.2) @` (U `*` V).
Proof.
apply/seteqP; split.
- move=> p [hx hy]; exists (first p,second p)=> //=.
  by rewrite (metric_product_pair_coordinates hp).
- move=> p [[x y] [hx hy] <-].
  by rewrite /metric_product_rectangle /= (metric_product_first_pair hp) (metric_product_second_pair hp); split.
Qed.

(** Source for [metric_product_rectangle_empty_left]: supporting
    empty-product convention for the measure gamma
    in 2.10.45, p. 202. *)
Lemma metric_product_rectangle_empty_left (P X Y : Type) (first : P -> X) (second : P -> Y) V :
  metric_product_rectangle first second set0 V=set0.
Proof. by rewrite /metric_product_rectangle preimage_set0 set0I. Qed.

(** Source for [metric_product_rectangle_empty_right]: supporting
    zero-mass empty second factor in 2.10.45,
    pp. 202–203. *)
Lemma metric_product_rectangle_empty_right (P X Y : Type) (first : P -> X) (second : P -> Y) U :
  metric_product_rectangle first second U set0=set0.
Proof. by rewrite /metric_product_rectangle preimage_set0 setI0. Qed.
