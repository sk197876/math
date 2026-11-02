(** Scalar-coordinate rectangles supporting Federer (1969), 2.8.20, p. 152.
    The plane's product Lebesgue measure is identified with the established
    Euclidean L^2 by EuclideanPlaneLebesgue.v. Closed rectangles are the
    target sets; half-open strips only establish finite disjoint volume
    bounds inside the Bohr fans. Saks1934 Lemma B, pp. 258–259, and
    Cesari1939 Lemma III, pp. 306–307, use these finite rectangle
    decompositions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureFiniteClosure
  LebesgueScalarMeasure EuclideanLebesgueBoxes HalfOpenIntervalAgreement
  ProductMeasure ProductRectangleValue ProductRectangleMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_plane_lebesgue]: the Cartesian L^2
    used in Federer 2.8.20, p. 152, with the product
    convention of 2.6.5, p. 120.
    This is notation for the already sealed product measure. *)
Definition scalar_plane_lebesgue (R : realType) :=
  product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R).

(** Source for [scalar_closed_rectangle]: the Cartesian
    products of compact intervals in Federer 2.8.20,
    p. 152. Nondegeneracy will be required of the
    counterexample's eligible sets, not of this supporting formula. *)
Definition scalar_closed_rectangle (R : realType) (a b c d : R) : set (R*R) :=
  `[a,b] `*` `[c,d].

(** Source for [scalar_half_open_strip]: supporting disjoint
    strips inside the finite rectangular constructions of
    Saks1934 Lemma B, pp. 258–259, and Cesari1939
    Lemma III, p. 306, for Federer 2.8.20, p. 152.
    Only the first coordinate is half-open. *)
Definition scalar_half_open_strip (R : realType) (a b c d : R) : set (R*R) :=
  `[a,b[ `*` `[c,d].

(** Source for [scalar_plane_lebesgue_is_measure]: the measure laws
    for the L^2 used in Federer 2.8.20, p. 152,
    supplied by the product formula 2.6.2, p. 115. *)
Lemma scalar_plane_lebesgue_is_measure (R : realType) : is_measure (@scalar_plane_lebesgue R).
Proof. exact: product_measure_is_measure. Qed.

(** Source for [lebesgue_scalar_half_open_value]: supporting
    strip length for the finite rectangle volumes in Federer
    2.8.20, p. 152. Open and closed intervals of the
    same endpoints have equal length, so the intermediate
    half-open interval has that length as well. *)
Lemma lebesgue_scalar_half_open_value (R : realType) (a b : R) :
  (a <= b)%R -> lebesgue_scalar_measure `[a,b[ = (b-a)%:E.
Proof.
move=> hab; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -lebesgue_scalar_segment //.
  apply: (@measure_mono R R _ (lebesgue_scalar_is_measure R)).
  move=> x; rewrite /= !in_itv /= => /andP [h1 h2]; by rewrite h1 (ltW h2).
- rewrite -lebesgue_scalar_open_interval //.
  apply: (@measure_mono R R _ (lebesgue_scalar_is_measure R)).
  move=> x; rewrite /= !in_itv /= => /andP [h1 h2]; by rewrite (ltW h1) h2.
Qed.

(** Source for [scalar_closed_rectangle_measurable]: the
    rectangles of Federer 2.8.20, p. 152, are
    Lebesgue measurable, by the product laws of 2.6.2,
    p. 115. Empty and degenerate rectangles are included. *)
Lemma scalar_closed_rectangle_measurable (R : realType) (a b c d : R) :
  measure_measurable (@scalar_plane_lebesgue R) (scalar_closed_rectangle a b c d).
Proof.
apply: product_measure_rectangle_measurable; exact: lebesgue_scalar_segment_measurable.
Qed.

(** Source for [scalar_closed_rectangle_value]: the area
    of the rectangles supporting Federer 2.8.20, p. 152,
    from the product formula 2.6.2(2), p. 115,
    and scalar interval lengths 2.5.17, p. 111. *)
Lemma scalar_closed_rectangle_value (R : realType) (a b c d : R) :
  (a <= b)%R -> (c <= d)%R ->
  scalar_plane_lebesgue (scalar_closed_rectangle a b c d) = ((b-a)*(d-c))%:E.
Proof.
move=> hab hcd.
have hv := @product_measure_rectangle_value R R R
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R) `[a,b] `[c,d]
  (@lebesgue_scalar_segment_measurable R a b) (@lebesgue_scalar_segment_measurable R c d).
by rewrite /scalar_plane_lebesgue /scalar_closed_rectangle hv
  (@lebesgue_scalar_segment R a b hab) (@lebesgue_scalar_segment R c d hcd) -EFinM.
Qed.

(** Source for [scalar_half_open_strip_measurable]: supporting
    measurable strips in the finite fan-volume estimate for
    Federer 2.8.20, p. 152. Half-open endpoints are
    local disjointness bookkeeping, not a change to the closed
    eligible rectangles in the book. *)
Lemma scalar_half_open_strip_measurable (R : realType) (a b c d : R) :
  measure_measurable (@scalar_plane_lebesgue R) (scalar_half_open_strip a b c d).
Proof.
apply: product_measure_rectangle_measurable; last exact: lebesgue_scalar_segment_measurable.
apply: lebesgue_scalar_borel_measurable; exact: half_open_interval_borel.
Qed.

(** Source for [scalar_half_open_strip_value]: supporting
    strip area for the finite rectangle construction in
    Federer 2.8.20, p. 152; Saks1934 Lemma B,
    pp. 258–259. Endpoints do not affect the area. *)
Lemma scalar_half_open_strip_value (R : realType) (a b c d : R) :
  (a <= b)%R -> (c <= d)%R ->
  scalar_plane_lebesgue (scalar_half_open_strip a b c d) = ((b-a)*(d-c))%:E.
Proof.
move=> hab hcd.
have hm1 : measure_measurable (@lebesgue_scalar_measure R) `[a,b[.
  apply: lebesgue_scalar_borel_measurable; exact: half_open_interval_borel.
have hv := @product_measure_rectangle_value R R R
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R) `[a,b[ `[c,d]
  hm1 (@lebesgue_scalar_segment_measurable R c d).
by rewrite /scalar_plane_lebesgue /scalar_half_open_strip hv
  (@lebesgue_scalar_half_open_value R a b hab) (@lebesgue_scalar_segment R c d hcd) -EFinM.
Qed.

(** Source for [is_nondegenerate_scalar_rectangle]: the family
    F of products of compact nondegenerate intervals in
    Federer 2.8.20, p. 152. This predicate specifies
    the set by an interval representation; it neither chooses
    endpoints nor identifies a unique representation. *)
Definition is_nondegenerate_scalar_rectangle (R : realType) (S : set (R*R)) :=
  exists a b c d : R, (a < b)%R /\ (c < d)%R /\ S = scalar_closed_rectangle a b c d.

(** Source for [nondegenerate_scalar_rectangle_positive]:
    positive area of the eligible rectangles in Federer
    2.8.20, p. 152, from the previously proved
    product volume formula. This supporting law excludes
    degenerate intervals from the counterexample's family. *)
Lemma nondegenerate_scalar_rectangle_positive (R : realType) (S : set (R*R)) :
  is_nondegenerate_scalar_rectangle S -> 0 < scalar_plane_lebesgue S.
Proof.
move=> [a [b [c [d [hab [hcd ->]]]]]].
by rewrite scalar_closed_rectangle_value ?ltW // lte_fin mulr_gt0 ?subr_gt0.
Qed.

(** Source for [nondegenerate_scalar_rectangle_finite]: finite
    area of the rectangles of Federer 2.8.20, p. 152,
    from the product formula. This is supporting boundedness
    of each individual rectangle, not a uniform family bound. *)
Lemma nondegenerate_scalar_rectangle_finite (R : realType) (S : set (R*R)) :
  is_nondegenerate_scalar_rectangle S -> scalar_plane_lebesgue S < +oo.
Proof.
move=> [a [b [c [d [hab [hcd ->]]]]]].
by rewrite scalar_closed_rectangle_value ?ltW // ltry.
Qed.
