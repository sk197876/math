(** Area bookkeeping for the remaining regions supporting
    Federer (1969), 2.8.20, p. 152; Saks1934
    Lemma B, p. 258, and Cesari1939 Lemma III,
    p. 306. Only the finite disjoint partition
    laws and already proved measure additivity are used.
    Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles
  FiniteHalfOpenPartitionUP MeasureUP MeasureBasic MeasureIndexedCover MeasureDisjointSupport
  MeasureCountableClosure NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_half_open_rectangle_measurable]:
    supporting measurability of remaining regions for Federer
    2.8.20, p. 152. Positivity is part of the
    region specification; measurability follows from interval products. *)
Lemma positive_half_open_rectangle_measurable (R : realType) (Q : set (R*R)) :
  is_nondegenerate_half_open_rectangle Q -> measure_measurable (@scalar_plane_lebesgue R) Q.
Proof.
move=> [a [b [c [d [_ [_ ->]]]]]]; exact: scalar_half_open_rectangle_measurable.
Qed.

(** Source for [positive_half_open_rectangle_area]: finite
    positive area of the remaining regions supporting Federer
    2.8.20, p. 152, from the side-length formula. *)
Lemma positive_half_open_rectangle_area (R : realType) (Q : set (R*R)) :
  is_nondegenerate_half_open_rectangle Q ->
  0<scalar_plane_lebesgue Q /\ scalar_plane_lebesgue Q \is a fin_num.
Proof.
move=> [a [b [c [d [hab [hcd ->]]]]]].
rewrite scalar_half_open_rectangle_value ?ltW // fin_numE; split=> //.
by rewrite lte_fin mulr_gt0 ?subr_gt0.
Qed.

(** Source for [finite_half_open_partition_area_sum]: supporting
    exact sum of remaining-region areas for Federer 2.8.20,
    p. 152; Saks1934 Lemma B, p. 258.
    Empty partitions are included. *)
Lemma finite_half_open_partition_area_sum (R : realType) (A : set (R*R))
    (G : set (set (R*R))) :
  is_finite_half_open_partition A G ->
  nonnegative_sum G (@scalar_plane_lebesgue R) = scalar_plane_lebesgue A.
Proof.
move=> hp; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@measure_disjoint_sum_bound R [the choiceType of (R*R)%type]
    [the choiceType of set (R*R)] (@scalar_plane_lebesgue R)
    (scalar_plane_lebesgue_is_measure R) A G idfun).
  + move=> S hS; exact (@half_open_partition_member_subset R A G hp S hS).
  + move=> S hS; apply: positive_half_open_rectangle_measurable.
    exact (@half_open_partition_rectangles R A G hp S hS).
  + exact: half_open_partition_disjoint hp.
- apply: (@measure_indexed_cover R [the choiceType of (R*R)%type]
    [the choiceType of set (R*R)] (@scalar_plane_lebesgue R)
    (scalar_plane_lebesgue_is_measure R) A G idfun).
  + exact: finite_set_countable (half_open_partition_finite hp).
  + by rewrite (half_open_partition_union hp).
Qed.
