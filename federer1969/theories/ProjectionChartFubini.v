(** Federer (1969), 2.10.46, p. 203: Fubini along an orthogonal projection,
    derived from the abstract adapted chart and the Euclidean block measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  OrthogonalProjectionChartUP EuclideanBlockCoordinates EuclideanBlockMeasure
  EuclideanLebesgueDimensions EuclideanLebesgueLinear MeasureUP MeasurePushforward
  ProductMeasure ProductSections ProductSetFubini PushforwardMeasurableSets
  CountablyMeasurableUP CountablyMeasurableSubsets CountablyMeasurableProduct
  PartialFunctionBasic MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ChartFubini.
Variable R : realType.
Variables m k : nat.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variables p : {linear R_n R (m+k) -> R_n R k}.
Variables f g : {linear R_n R (m+k) -> R_n R (m+k)}.
Hypothesis hc : is_orthogonal_projection_chart p f g.
Local Notation F := ((@euclidean_block_split R m k) \o f).
Local Notation H := (g \o (@euclidean_block_join R m k)).
Local Notation Leb n := (@euclidean_lebesgue_measure R n).
Local Notation ha := (euclidean_lebesgue_is_measure R m).
Local Notation hb := (euclidean_lebesgue_is_measure R k).

(** Source for [projection_chart_product_measure]: supporting
    product-measure identity for the Fubini step in 2.10.46,
    p. 203, by orthogonal invariance and 2.6.5, p. 120. *)
Theorem projection_chart_product_measure :
  measure_pushforward F (Leb (m+k))=product_measure ha hb.
Proof.
apply: funext=> A.
change (Leb (m+k) (f @^-1` ((@euclidean_block_split R m k) @^-1` A))=
  product_measure ha hb A).
rewrite (@euclidean_orthogonal_pushforward R (m+k) f (projection_chart_orthogonal_law hc)).
exact (congr1 (fun mu=>mu A) (@euclidean_block_measure R m k)).
Qed.

(** Source for [projection_chart_section_integral]: supporting
    horizontal-section integral for the projected-volume bound in
    2.10.46, p. 203. Every Lebesgue-measurable set is
    allowed; Euclidean sigma finiteness is proved, not assumed. *)
Theorem projection_chart_section_integral (S : set (E (m+k))) :
  measure_measurable (Leb (m+k)) S ->
  is_measure_integral (Leb k)
    (partial_function_total (fun y=>Leb m
      (product_horizontal_section (H @^-1` S) y))) (Leb (m+k) S).
Proof.
move=> hS; pose K := H @^-1` S.
have hpre : F @^-1` K=S.
  apply/seteqP; split=> x;
    change (S (g (euclidean_block_join (euclidean_block_split (f x))))->S x) ||
    change (S x->S (g (euclidean_block_join (euclidean_block_split (f x)))));
    by rewrite euclidean_block_splitK (projection_chart_forward_inverse_law hc).
have hK : measure_measurable (product_measure ha hb) K.
  rewrite -projection_chart_product_measure.
  apply: pushforward_measurable_from_preimage; by rewrite hpre.
have hKc : measure_countably_measurable (product_measure ha hb) K.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb) hK (subsetT K)).
  exact: product_whole_countably_measurable (euclidean_lebesgue_countably_measurable R m)
    (euclidean_lebesgue_countably_measurable R k).
have hi := (@product_set_fubini R [the choiceType of E m] [the choiceType of E k]
  (Leb m) (Leb k) ha hb K hKc).2.2.2.
have hmass : product_measure ha hb K=Leb (m+k) S.
  by rewrite -projection_chart_product_measure /measure_pushforward hpre.
by rewrite hmass in hi.
Qed.
End ChartFubini.
