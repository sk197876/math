(** Federer (1969), 3.3.19, p. 302: actual vectors
    exp(i t) in the Euclidean plane. The opaque scalar
    trigonometric system supplies only elementary background;
    the geometric identities are proved here. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric PlanarCircleCapCoordinates
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Circle.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_unit_vector]: the actual planar
    exp(i t) supporting the original centres in 3.3.19,
    p. 302; no new ambient metric is used. *)
Definition circular_unit_vector (t:R):E:=
  [ffun i=>if i==ord0 then C t else S t].

(** Source for [circular_unit_vector_first]: first original
    coordinate of exp(i t), 3.3.19, p. 302. *)
Lemma circular_unit_vector_first t:circular_unit_vector t ord0=C t.
Proof. by rewrite /circular_unit_vector ffunE eqxx. Qed.

(** Source for [circular_unit_vector_second]: second original
    coordinate of exp(i t), 3.3.19, p. 302. *)
Lemma circular_unit_vector_second t:
  circular_unit_vector t (@Ordinal 2 1 (erefl true))=S t.
Proof. by rewrite /circular_unit_vector ffunE. Qed.

(** Source for [circular_cosine_difference]: scalar difference
    identity supporting the centre separation in 3.3.19,
    p. 302, derived only from public circular laws. *)
Lemma circular_cosine_difference a b:C (a-b)=C a*C b+S a*S b.
Proof.
by rewrite (circular_trig_cosine_add ht) (circular_trig_cosine_even ht)
  (real_sine_odd hb) mulrN opprK.
Qed.

(** Source for [circular_unit_vector_inner]: the actual
    Euclidean dot product of two circular directions,
    supporting 3.3.19, p. 302. *)
Lemma circular_unit_vector_inner a b:
  euclidean_inner_product (circular_unit_vector a) (circular_unit_vector b)=C (a-b).
Proof.
by rewrite planar_euclidean_inner_coordinates !circular_unit_vector_first
  !circular_unit_vector_second circular_cosine_difference.
Qed.

(** Source for [circular_unit_vector_norm]: every actual
    circular direction has norm one, 3.3.19, p. 302. *)
Lemma circular_unit_vector_norm t:
  inner_norm (@euclidean_inner_productP R 2) (circular_unit_vector t)= 1.
Proof.
apply:inner_norm_value;first exact:ler01.
rewrite expr1n planar_euclidean_inner_coordinates circular_unit_vector_first
  circular_unit_vector_second -!expr2.
exact:(esym (circular_trig_unit ht t)).
Qed.

(** Source for [circular_unit_vector_distance_square]: exact
    squared chord supporting the minimum centre distance
    in 3.3.19, p. 302, for arbitrary original angles. *)
Lemma circular_unit_vector_distance_square a b:
  mdist (circular_unit_vector a) (circular_unit_vector b)^+2= 2-2*C (a-b).
Proof.
rewrite inner_metric_distanceE inner_norm_sqr planar_euclidean_inner_coordinates
  !ffunE /=.
have hA:=circular_trig_unit ht a;have hB:=circular_trig_unit ht b.
rewrite circular_cosine_difference; nra.
Qed.

(** Source for [circular_unit_vector_period]: exact full-period
    identity for the circular children of 3.3.19, p. 302.
    Thus indexing k= 0,...,n-1 agrees with book k= 1,...,n. *)
Lemma circular_unit_vector_period t:circular_unit_vector (t+(p+p))=circular_unit_vector t.
Proof.
apply/ffunP=>i;rewrite /circular_unit_vector !ffunE addrA.
case:ifP=>_.
- by rewrite !(real_cosine_half_period hb) opprK.
- by rewrite !(real_sine_half_period hb) opprK.
Qed.
End Circle.
