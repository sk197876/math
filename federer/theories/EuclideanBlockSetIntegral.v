(** The actual block-coordinate set form of Fubini used
    in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanBlockMeasure EuclideanLebesgueDimensions EuclideanLebesgueBoxes MeasureUP MeasurePushforward
  PushforwardMeasurableSets ProductMeasure ProductSections ProductSetFubini CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct PartialFunctionBasic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_set_integral]: supporting
    first volume identity in Federer 3.2.45,
    p. 279. Apply the already proved set Fubini
    theorem, 2.6.2(3), p. 115, through the
    original block measure of 2.6.5, p. 120.
    Euclidean sigma finiteness supplies its countable
    measurability hypothesis. Every measurable source
    and both empty coordinate blocks remain. *)
Theorem euclidean_block_set_integral (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R (m+n)))) :
  measure_measurable (@euclidean_lebesgue_measure R (m+n)) S ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y => @euclidean_lebesgue_measure R n
      [set z | S (@euclidean_block_join R m n (y,z))]))
    (@euclidean_lebesgue_measure R (m+n) S).
Proof.
move=> hS.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose A := (@euclidean_block_join R m n) @^-1` S.
pose ha := euclidean_lebesgue_is_measure R m.
pose hb := euclidean_lebesgue_is_measure R n.
have hPreimage : (@euclidean_block_split R m n) @^-1` A=S.
  apply/seteqP; split=> x; by rewrite /A /= euclidean_block_splitK.
have hA : measure_measurable (product_measure ha hb) A.
  rewrite -euclidean_block_measure.
  apply: pushforward_measurable_from_preimage; by rewrite hPreimage.
have hCount : measure_countably_measurable (product_measure ha hb) A.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb) hA (subsetT A)).
  exact: product_whole_countably_measurable (euclidean_lebesgue_countably_measurable R m)
    (euclidean_lebesgue_countably_measurable R n).
have h := (@product_set_fubini R X Y (@euclidean_lebesgue_measure R m)
  (@euclidean_lebesgue_measure R n) ha hb A hCount).2.2.1.
have hMass : product_measure ha hb A= @euclidean_lebesgue_measure R (m+n) S.
  by rewrite -euclidean_block_measure /measure_pushforward hPreimage.
by rewrite hMass in h.
Qed.
