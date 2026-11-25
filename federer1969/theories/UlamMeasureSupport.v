(** Federer (1969), 2.2.16, pp. 71–72, second assertion: a finite
    Borel-measurable metric measure is concentrated on its support if the
    space has a dense subset of Ulam cardinality. Use only the sealed open
    null cover and separated closed refinement interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSupport UlamCardinalUP
  DenseUlamSupportCoverUP DenseUlamSupportCoverSealed UlamOpenNullUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_ulam_dense_support_complement_null]:
    direct second conclusion of Federer 2.2.16, pp. 71–72.
    No Radon or completeness hypothesis is added. The Ulam
    condition is on a dense subset of the ambient space,
    not merely on the support whose separability was proved first. *)
Theorem finite_measure_ulam_dense_support_complement_null (R : realType)
    (X : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set X) : mu setT < +oo ->
  (forall V, open V -> measure_measurable mu V) -> dense D -> is_ulam_set R D ->
  mu (~` measure_support mu) = 0.
Proof.
move=> hf ho hd hu.
pose w := @DenseUlamSupportCover.value R X mu hm D hd hu.
have hw := @DenseUlamSupportCover.laws R X mu hm D hd hu.
rewrite -(@ulam_open_cover_union R X [the choiceType of (X * nat)%type]
  mu (~` measure_support mu) w.1 w.2 hw).
exact: (@ulam_indexed_open_null_union R X [the choiceType of (X * nat)%type] mu hm
  w.1 w.2 hf ho (ulam_open_cover_indices hw) (ulam_open_cover_open hw) (ulam_open_cover_null hw)).
Qed.
