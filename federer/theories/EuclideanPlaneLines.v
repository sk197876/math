(** The horizontal and vertical coordinate lines of Federer (1969), 2.5.10,
    p. 101, in the actual Euclidean coordinate space of 1.7.1, p. 28. These
    identities connect the Cartesian presentation with the previously proved
    Hausdorff length of affine coordinate lines. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanOneCoordinate EuclideanCoordinateSplit EuclideanPlaneCoordinates EuclideanCoordinateMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_plane_join_head]: first
    coordinate of (s,t), the projection used in
    Federer 2.5.10, p. 101. *)
Lemma euclidean_plane_join_head (R : realType) (s t : R) :
  euclidean_plane_join (s,t) ord0=s.
Proof. by rewrite /euclidean_plane_join euclidean_join_head. Qed.

(** Source for [euclidean_plane_join_tail]: second
    coordinate of (s,t), supporting the vertical-line
    test in Federer 2.5.10, p. 101. *)
Lemma euclidean_plane_join_tail (R : realType) (s t : R) (i : 'I_1) :
  euclidean_plane_join (s,t) (lift ord0 i)=t.
Proof. by rewrite /euclidean_plane_join euclidean_join_tail /euclidean_one_embed ffunE. Qed.

(** Source for [euclidean_coordinate_line_value]: supporting
    scalar-coordinate formula for the affine line tests
    in Federer 2.5.10, p. 101, from the
    coordinate vector operations of 1.7.1, p. 28. *)
Lemma euclidean_coordinate_line_value (R : realType) n (i j : 'I_n)
    (v : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
  euclidean_coordinate_line i v t j=v j+t*(if j==i then 1 else 0).
Proof. by rewrite /euclidean_coordinate_line /coordinate_basis !ffunE. Qed.

(** Source for [euclidean_plane_horizontal_line]: affine
    coordinate-line description of the horizontal tests
    for the density in Federer 2.5.10, p. 101. *)
Lemma euclidean_plane_horizontal_line (R : realType) (s t : R) :
  euclidean_plane_join (s,t)=euclidean_coordinate_line ord0 (euclidean_plane_join (0,t)) s.
Proof.
apply/ffunP=> i.
rewrite euclidean_coordinate_line_value.
case: (unliftP ord0 i)=> [j ->|->].
- by rewrite !euclidean_plane_join_tail lift_eqF mulr0 addr0.
- by rewrite !euclidean_plane_join_head eqxx mulr1 add0r.
Qed.

(** Source for [euclidean_plane_vertical_line]: affine
    coordinate-line description of the vertical tests
    for the density in Federer 2.5.10, p. 101. *)
Lemma euclidean_plane_vertical_line (R : realType) (s t : R) :
  euclidean_plane_join (s,t)=euclidean_coordinate_line (lift ord0 ord0) (euclidean_plane_join (s,0)) t.
Proof.
apply/ffunP=> i.
rewrite euclidean_coordinate_line_value.
case: (unliftP ord0 i)=> [j ->|->].
- by rewrite !euclidean_plane_join_tail (ord1 j) eqxx mulr1 add0r.
- by rewrite !euclidean_plane_join_head eq_sym lift_eqF mulr0 addr0.
Qed.
