(** Federer (1969), 3.2.11, p. 249: reduce Borel
    source sets to countably many finite-mass Borel pieces,
    using sigma finiteness and Borel regularity of Lebesgue
    measure. This supporting result does not select a partition. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes TopologicalBorel BorelPartition BorelSubordinatePartition
  BorelRegularMeasureUP CountablyMeasurableUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_finite_borel_partition_exists]:
    the finite-source reductions in Federer 3.2.11,
    p. 249. Any Borel source set has a
    countable Borel partition into finite Lebesgue-mass members,
    including zero-dimensional and empty source sets. *)
Theorem euclidean_finite_borel_partition_exists (R:realType) m
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  borel_set A ->exists H,is_borel_partition A H /\
    forall B,H B ->euclidean_lebesgue_measure m B< +oo.
Proof.
move=>hA.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose hr:=euclidean_lebesgue_borel_regular R m.
have [F [hCount [hUnion hFinite]]]:=euclidean_lebesgue_countably_measurable R m.
have hex B:exists C:set X,B `<=` C /\borel_set C /\mu B=mu C.
  exact (@borel_regular_cover R [the topologicalType of X] mu hr B).
have [C hC]:=choice hex.
pose G:=C @` F.
have hG:countable G:=sub_countable (card_image_le C F) hCount.
have hGB B:G B ->borel_set B by move=>[D hD <-]; exact (hC D).2.1.
have hGF B:G B ->mu B< +oo.
  move=>[D hD <-]; rewrite -(hC D).2.2; exact (hFinite D hD).2.
have hCover:A `<=`\bigcup_(B in G) B.
  move=>x hx.
  have hWhole:(\bigcup_(D in F) D) x by rewrite -hUnion.
  have [D hD hxD]:=hWhole; exists (C D); first by exists D.
  exact ((hC D).1 x hxD).
have [H [hH hSub]]:=borel_countable_cover_subordinate_partition hA hG hGB hCover.
exists H; split=> //; move=>B hB.
have [_ [D [hD hBD]]]:=hSub B hB.
exact (le_lt_trans (measure_mono hm hBD) (hGF D hD)).
Qed.
