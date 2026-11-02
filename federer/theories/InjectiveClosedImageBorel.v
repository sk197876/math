(** Federer (1969), 2.2.10(2), p. 67: if f maps a complete separable metric
    space continuously into a Hausdorff space and is one-to-one on a closed
    C, then f(C) is Borel. This public proof uses only the sealed trees and
    their abstract consequences. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP ClosedCoverTreeUP ClosedCoverTreeSealed
  CoverPartitionTreeUP CoverPartitionTreeSealed BorelImageTreeUP BorelImageTreeSealed
  BorelImageTreeBasic BorelImageTreeEquality TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [injective_closed_image_borel]: direct assertion (2) in
    Federer 2.2.10, p. 67. All printed hypotheses are retained; the closed
    set and source may be empty. The image is identified with the countable
    intersection of Borel level unions. *)
Theorem injective_closed_image_borel (R : realType) (T : metricType R)
    (Y : topologicalType) (f : T -> Y) (C : set T) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) -> hausdorff_space Y -> continuous f ->
  closed C -> (forall x y, C x -> C y -> f x = f y -> x = y) -> borel_set (f @` C).
Proof.
move=> hT [H [hc hd]] hY hf hC hinj.
case: (pselect (C !=set0))=> [hnC|hnC].
- have hnT : (@setT T) !=set0 by have [x _] := hnC; exists x.
  pose E := @ClosedCoverTree.value R T H hc hd hnT.
  have hE : is_closed_cover_tree E := @ClosedCoverTree.laws R T H hc hd hnT.
  pose A := @CoverPartitionTree.value T E.
  have hA : is_cover_partition_tree E A := @CoverPartitionTree.laws T E.
  have hsep : exists D : set T, countable D /\ dense D by exists H.
  pose B := @BorelImageTree.value R T Y f C E A hE hA hT hsep hY hf hC hinj.
  have hB : is_borel_image_tree f C E A B :=
    @BorelImageTree.laws R T Y f C E A hE hA hT hsep hY hf hC hinj.
  rewrite -(@borel_image_tree_target_eq R T Y f C E A B hE hA hB hT hY hf hC).
  exact: (@borel_image_tree_target_borel T Y f C E A B hB).
- have he : f @` C = set0.
    apply/seteqP; split=> [y [x hx _]|y []].
    exfalso; apply: hnC; by exists x.
  rewrite he; exact: open_borel_set (@open0 Y).
Qed.
