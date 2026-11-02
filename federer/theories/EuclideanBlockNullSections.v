(** Federer (1969), 3.2.21, p. 257: Fubini
    converts null mu-dimensional sections of a Borel set into
    ambient null mass. This records the erratum's dimension
    correction: the section mass is L^mu, not L^m. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanLebesgueDimensions
  MeasureUP MeasureBasic MeasurePushforward PushforwardMeasurableSets
  ProductMeasure ProductSections ProductSetFubini MeasureAlmostBasic
  MeasureIntegralUniqueness MeasureConullZeroIntegral CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_null_sections]: Fubini step in
    Federer 3.2.21, p. 257, with first block k and
    section dimension mu. The printed first-block convention
    is obtained by a fixed block interchange. Empty blocks
    are allowed in this supporting assertion. Erratum p. 5,
    book p. 257 line 26: use L^mu on each section. *)
Lemma euclidean_block_null_sections (R:realType) k mu
    (A:set (inner_metric_space (@euclidean_inner_productP R (k+mu)))):
  measure_measurable (@euclidean_lebesgue_measure R (k+mu)) A ->
  (forall y:R_n R k,@euclidean_lebesgue_measure R mu
    [set z:R_n R mu|A (euclidean_block_join (y,z))]=0%E) ->
  @euclidean_lebesgue_measure R (k+mu) A=0%E.
Proof.
move=>hA hSections.
pose X:=inner_metric_space (@euclidean_inner_productP R k).
pose Y:=inner_metric_space (@euclidean_inner_productP R mu).
pose ha:=euclidean_lebesgue_is_measure R k.
pose hb:=euclidean_lebesgue_is_measure R mu.
pose rho:=product_measure ha hb.
pose S:set (X*Y)%type:=fun p=>A (euclidean_block_join p).
have hPre:(@euclidean_block_split R k mu) @^-1` S=A.
  apply/seteqP; split=>x hx.
  - change (A (euclidean_block_join (euclidean_block_split x))) in hx.
    by rewrite euclidean_block_splitK in hx.
  - change (A (euclidean_block_join (euclidean_block_split x))).
    by rewrite euclidean_block_splitK.
have hSm:measure_measurable rho S.
  rewrite /rho /ha /hb -euclidean_block_measure; apply: pushforward_measurable_from_preimage.
  by rewrite hPre.
have hSc:measure_countably_measurable rho S.
  apply:(measurable_subset_countably_measurable (product_measure_is_measure ha hb)
    hSm (fun _ _=>Logic.I)).
  exact (@product_whole_countably_measurable R [the choiceType of X]
    [the choiceType of Y] _ _ ha hb (euclidean_lebesgue_countably_measurable R k)
    (euclidean_lebesgue_countably_measurable R mu)).
have hZero:rho S=0%E.
  have hi:=(@product_set_fubini R [the choiceType of X] [the choiceType of Y]
    _ _ ha hb S hSc).2.2.1.
  apply:(measure_integral_unique hi _); apply:(measure_almost_zero_integral ha).
  apply:(measure_almost_everywhere_mono ha _ (measure_almost_everywhere_true ha))=>y _.
  exact:hSections.
rewrite /rho /ha /hb -euclidean_block_measure /measure_pushforward hPre in hZero.
exact hZero.
Qed.
