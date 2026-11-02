(** Federer (1969), 2.2.7, p. 64: the segment a+t(b-a) used in the
    convex-domain proof. These supporting identities follow from the
    abstract norm and vector-space laws. The previously defined convexity
    predicate is independent of an inner product, despite its historical
    name. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_segment_point]: Federer 2.2.7, p. 64,
    the explicitly printed segment parametrisation a+t(b-a). *)
Definition metric_segment_point (R : realType) (V : lmodType R)
    (a b : V) (t : R) : V := a + t *: (b-a).

(** Source for [metric_segment_zero]: supporting endpoint identity
    for the set S in Federer 2.2.7, p. 64: at parameter zero
    the segment starts at a. *)
Lemma metric_segment_zero (R : realType) (V : lmodType R) (a b : V) :
  metric_segment_point a b 0 = a.
Proof. by rewrite /metric_segment_point scale0r addr0. Qed.

(** Source for [metric_segment_one]: supporting endpoint identity
    for Federer 2.2.7, p. 64: at parameter one the segment ends at b. *)
Lemma metric_segment_one (R : realType) (V : lmodType R) (a b : V) :
  metric_segment_point a b 1 = b.
Proof. by rewrite /metric_segment_point scale1r addrCA subrr addr0. Qed.

(** Source for [metric_segment_in_convex]: Federer 2.2.7,
    p. 64, the convexity hypothesis ensures that every parameter
    between zero and one belongs to the original domain. *)
Lemma metric_segment_in_convex (R : realType) (V : lmodType R)
    (X : set V) (hX : is_inner_convex X) a b t :
  X a -> X b -> 0 <= t -> t <= 1 -> X (metric_segment_point a b t).
Proof.
move=> ha hb ht0 ht1; have hc := hX a b ha hb t ht0 ht1.
have he : metric_segment_point a b t = (1-t) *: a + t *: b.
  by rewrite /metric_segment_point scalerBr scalerBl scale1r addrA addrAC.
by rewrite he.
Qed.

(** Source for [metric_segment_difference]: supporting algebra
    for Federer 2.2.7, p. 64: the difference of two segment
    points is (s-t)(b-a). *)
Lemma metric_segment_difference (R : realType) (V : lmodType R)
    (a b : V) s t :
  metric_segment_point a b s - metric_segment_point a b t = (s-t) *: (b-a).
Proof. by rewrite /metric_segment_point opprD addrACA subrr add0r -scalerBl. Qed.

(** Source for [metric_segment_distance]: Federer 2.2.7,
    p. 64, the norm distance along the segment is |s-t| times
    |b-a|, explaining the factors in the printed supremum argument. *)
Lemma metric_segment_distance (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a b : real_norm_metric_space hN) s t :
  mdist (metric_segment_point a b s) (metric_segment_point a b t) = `|s-t| * N (b-a).
Proof.
by rewrite real_norm_metric_distanceE metric_segment_difference (real_seminorm_scale hN.1).
Qed.
