(** Half-open auxiliary boxes for the finite Bohr packing
    supporting Federer (1969), 2.8.20, p. 152.
    The eligible rectangles remain compact products of closed
    nondegenerate intervals. Half-open companions serve only to
    partition remaining regions without boundary overlaps; their
    areas and finite-union areas equal the closed counterparts.
    Saks1934 Lemma B, pp. 258–259, and Cesari1939
    Lemma III, pp. 306–307, use nonoverlapping regions.
    Exact source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic
  ProductMeasure ProductRectangleValue ProductRectangleMeasurability
  LebesgueScalarMeasure EuclideanLebesgueBoxes HalfOpenIntervalAgreement
  ScalarPlaneRectangles VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_half_open_rectangle]: auxiliary box
    for the disjoint regions in the construction supporting
    Federer 2.8.20, p. 152; Saks1934 Lemma B,
    p. 258. Its closed companion, not this half-open
    set, is an eligible compact rectangle in the book. *)
Definition scalar_half_open_rectangle (R : realType) (a b c d : R) : set (R*R) :=
  `[a,b[ `*` `[c,d[.

(** Source for [scalar_half_open_rectangle_measurable]: the
    auxiliary rectangles for Federer 2.8.20, p. 152,
    are measurable by the established product laws and Borel
    measurability of half-open scalar intervals. *)
Lemma scalar_half_open_rectangle_measurable (R : realType) (a b c d : R) :
  measure_measurable (@scalar_plane_lebesgue R) (scalar_half_open_rectangle a b c d).
Proof.
apply: product_measure_rectangle_measurable;
  apply: lebesgue_scalar_borel_measurable; exact: half_open_interval_borel.
Qed.

(** Source for [scalar_half_open_rectangle_value]: supporting
    auxiliary box areas for Federer 2.8.20, p. 152;
    Saks1934 Lemma B, pp. 258–259. Replacing a closed
    coordinate interval by its half-open companion preserves length. *)
Lemma scalar_half_open_rectangle_value (R : realType) (a b c d : R) :
  (a <= b)%R -> (c <= d)%R ->
  scalar_plane_lebesgue (scalar_half_open_rectangle a b c d) = ((b-a)*(d-c))%:E.
Proof.
move=> hab hcd.
have hm1 : measure_measurable (@lebesgue_scalar_measure R) `[a,b[.
  apply: lebesgue_scalar_borel_measurable; exact: half_open_interval_borel.
have hm2 : measure_measurable (@lebesgue_scalar_measure R) `[c,d[.
  apply: lebesgue_scalar_borel_measurable; exact: half_open_interval_borel.
have hv := @product_measure_rectangle_value R R R
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R) `[a,b[ `[c,d[ hm1 hm2.
by rewrite /scalar_plane_lebesgue /scalar_half_open_rectangle hv
  (@lebesgue_scalar_half_open_value R a b hab) (@lebesgue_scalar_half_open_value R c d hcd) -EFinM.
Qed.

(** Source for [half_open_rectangle_within_closed]: supporting
    companion inclusion for Federer 2.8.20, p. 152.
    Only the upper sides are removed from the closed rectangle. *)
Lemma half_open_rectangle_within_closed (R : realType) (a b c d : R) :
  scalar_half_open_rectangle a b c d `<=` scalar_closed_rectangle a b c d.
Proof.
move=> [x y]; rewrite /scalar_half_open_rectangle /scalar_closed_rectangle /= !in_itv /=.
move=> [/andP [hx1 hx2] /andP [hy1 hy2]]; split; by rewrite ?hx1 ?hy1 ?ltW.
Qed.

(** Source for [finite_equal_measure_difference_null]: supporting
    boundary-removal inference for the finite boxes in Federer
    2.8.20, p. 152. A measurable subset with the
    same finite measure leaves a null remainder, directly by
    the splitting law of 2.1.2, p. 54. *)
Lemma finite_equal_measure_difference_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A B : set X) :
  B `<=` A -> measure_measurable mu B -> mu A = mu B ->
  mu B \is a fin_num -> mu (A `\` B) = 0.
Proof.
move=> hBA hB heq hfin.
have hi : A `&` B = B.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hBA x hx.
have hs := hB A; rewrite hi heq in hs.
have h := congr1 (fun z => z - mu B) hs.
by move: h; rewrite subee // (addeC (mu B)) addeK // => ->.
Qed.

(** Source for [closed_rectangle_half_open_remainder_null]:
    the boundary bookkeeping for the Bohr construction supporting
    Federer 2.8.20, p. 152. Closed and half-open
    companions have equal finite area and differ by a null set. *)
Lemma closed_rectangle_half_open_remainder_null (R : realType) (a b c d : R) :
  (a <= b)%R -> (c <= d)%R ->
  scalar_plane_lebesgue (scalar_closed_rectangle a b c d `\` scalar_half_open_rectangle a b c d) = 0.
Proof.
move=> hab hcd.
apply: (@finite_equal_measure_difference_null R [the choiceType of (R*R)%type]
  (@scalar_plane_lebesgue R) (scalar_closed_rectangle a b c d) (scalar_half_open_rectangle a b c d)).
- exact: half_open_rectangle_within_closed.
- exact: scalar_half_open_rectangle_measurable.
- by rewrite scalar_closed_rectangle_value // scalar_half_open_rectangle_value.
- by rewrite scalar_half_open_rectangle_value // fin_numE.
Qed.

(** Source for [finite_closed_half_open_union_area]: supporting
    preservation of the fan-union area when replacing closed
    cells by half-open companions for Federer 2.8.20,
    p. 152. The difference is covered by the finite
    union of their null boundaries; overlaps need not be disjoint. *)
Lemma finite_closed_half_open_union_area (R : realType) (I : finType)
    (a b c d : I -> R) :
  (forall i, (a i <= b i)%R) -> (forall i, (c i <= d i)%R) ->
  scalar_plane_lebesgue (\bigcup_(i in @setT I) scalar_closed_rectangle (a i) (b i) (c i) (d i)) =
  scalar_plane_lebesgue (\bigcup_(i in @setT I) scalar_half_open_rectangle (a i) (b i) (c i) (d i)).
Proof.
move=> hab hcd.
pose F i := scalar_closed_rectangle (a i) (b i) (c i) (d i).
pose H i := scalar_half_open_rectangle (a i) (b i) (c i) (d i).
pose U := \bigcup_(i in @setT I) F i.
pose W := \bigcup_(i in @setT I) H i.
have hWU : W `<=` U.
  move=> x [i _ hx]; exists i=> //; exact: half_open_rectangle_within_closed hx.
have hcnt : countable (@setT I) := finite_set_countable (@finite_finset I setT).
have hn : scalar_plane_lebesgue (\bigcup_(i in @setT I) (F i `\` H i)) = 0.
  apply: (@measure_null_countable_union R [the choiceType of (R*R)%type] I
    (@scalar_plane_lebesgue R) (scalar_plane_lebesgue_is_measure R) setT (fun i => F i `\` H i) hcnt).
  move=> i _; exact: closed_rectangle_half_open_remainder_null (hab i) (hcd i).
have hUW : scalar_plane_lebesgue (U `\` W) = 0.
  apply: (@measure_null_subset R [the choiceType of (R*R)%type]
    (@scalar_plane_lebesgue R) (scalar_plane_lebesgue_is_measure R) _ _ _ hn).
  move=> x [[i _ hx] hnx]; exists i=> //; split=> //; move=> hH; apply: hnx; by exists i.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: null_remainder_measure_cover_bound (scalar_plane_lebesgue_is_measure R) hUW.
- exact (@measure_mono R [the choiceType of (R*R)%type] (@scalar_plane_lebesgue R)
    (scalar_plane_lebesgue_is_measure R) W U hWU).
Qed.

(** Source for [is_nondegenerate_half_open_rectangle]: auxiliary
    positive side-length regions for the finite Bohr packing
    supporting Federer 2.8.20, p. 152. These are
    partition pieces; their closed companions supply the
    compact eligible covering rectangles. *)
Definition is_nondegenerate_half_open_rectangle (R : realType) (S : set (R*R)) :=
  exists a b c d : R, (a < b)%R /\ (c < d)%R /\ S = scalar_half_open_rectangle a b c d.
