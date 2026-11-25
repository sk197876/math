(** Federer (1969), 3.2.41, printed p. 278, compact
    approximation: proper open box interiors of null-overlap
    closed cubes are genuinely disjoint. This supporting fact
    follows from the positive actual volume of an overlapping
    proper open box, not from disjointness modulo a null set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanOpenCoordinateBoxUP EuclideanOpenCoordinateBoxMeasure
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_box_intersection_positive_volume]: supporting
    actual positive intersection used for the elementary compact
    approximation of Federer 3.2.41, p. 278. A point in both
    original proper boxes gives a proper max/min endpoint box
    inside their intersection, including the positive R^0 atom. *)
Lemma open_box_intersection_positive_volume (R:realType) n (a b c d:R_n R n)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_open_coordinate_box a b A ->
  is_euclidean_open_coordinate_box c d B ->(A `&` B) !=set0 ->
  (0<@euclidean_lebesgue_measure R n (A `&` B))%E.
Proof.
move=> hA hB [x [hxA hxB]].
pose e:R_n R n:=[ffun i=>Order.max (a i) (c i)].
pose f:R_n R n:=[ffun i=>Order.min (b i) (d i)].
have hBounds i:e i<f i.
  have /andP[hax hxb]:=(hA.2 x).1 hxA i.
  have /andP[hcx hxd]:=(hB.2 x).1 hxB i.
  rewrite /e /f !ffunE lt_min !gt_max.
  by rewrite (lt_trans hax hxb) (lt_trans hcx hxb)
    (lt_trans hax hxd) (lt_trans hcx hxd).
have [C hC]:=euclidean_open_coordinate_box_exists hBounds.
have hSub:C `<=` A `&` B.
  move=> z hz.
  have hParts i:a i<z i<b i /\c i<z i<d i.
    have /andP[hLow hHigh]:=(hC.2 z).1 hz i.
    rewrite /e ffunE gt_max in hLow.
    rewrite /f ffunE lt_min in hHigh.
    split; apply/andP; split;
      [exact:(andP hLow).1|exact:(andP hHigh).1|
       exact:(andP hLow).2|exact:(andP hHigh).2].
  split.
  - apply:(hA.2 z).2=> i; exact:(hParts i).1.
  - apply:(hB.2 z).2=> i; exact:(hParts i).2.
have hPos:=(andP (open_coordinate_box_positive_finite_volume hC)).1.
exact:(lt_le_trans hPos (@measure_mono R _ _ (euclidean_lebesgue_is_measure R n) _ _ hSub)).
Qed.

(** Source for [open_boxes_null_intersection_disjoint]: supporting
    genuine disjointness of the finite open approximating family
    in Federer 3.2.41, p. 278. Nullity of an arbitrary overlap
    alone is not treated as disjointness; proper-box positivity
    proves that every shared point would be impossible. *)
Lemma open_boxes_null_intersection_disjoint (R:realType) n (a b c d:R_n R n)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_open_coordinate_box a b A ->
  is_euclidean_open_coordinate_box c d B ->
  @euclidean_lebesgue_measure R n (A `&` B)=0%E ->
  forall x,A x ->B x ->False.
Proof.
move=> hA hB hNull x hx hy.
have hNonempty:(A `&` B) !=set0 by exists x; split.
have hPos:=open_box_intersection_positive_volume hA hB hNonempty.
by rewrite hNull ltxx in hPos.
Qed.
