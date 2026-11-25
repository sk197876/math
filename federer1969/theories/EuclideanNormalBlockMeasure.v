(** Fubini in an orthogonal normal chart supporting Federer (1969), 2.10.30,
    p. 195. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  OrthogonalMaps EuclideanNormalChartUP EuclideanNormalBlockCoordinates
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanLebesgue
  EuclideanLebesgueDimensions EuclideanLebesgueLinear LebesgueScalarMeasure
  RealMetricBackground SteinerSymmetrisationUP ProductSections ProductMeasure ProductSetFubini
  MeasureUP MeasurePushforward PushforwardMeasurableSets CountablyMeasurableUP
  CountablyMeasurableSubsets CountablyMeasurableProduct PartialFunctionBasic
  MeasureIntegralUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section NormalMeasure.
Variable R : realType.
Variable n : nat.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).
Variable u : E (n+1).
Variable D : euclidean_normal_chart_data R (n+1).
Hypothesis hD : @is_euclidean_normal_chart R (n+1) (rshift n (ord0 : 'I_1)) u D.
Local Notation f := (normal_chart_forward_map D).
Local Notation g := (normal_chart_backward_map D).
Local Notation H := (@euclidean_normal_block_join R n D).
Local Notation F := (@euclidean_normal_block_split R n D).
Local Notation Leb k := (@euclidean_lebesgue_measure R k).
Local Notation ha := (euclidean_lebesgue_is_measure R n).
Local Notation hb := (euclidean_lebesgue_is_measure R 1).

(** Source for [euclidean_normal_block_pushforward]: supporting
    product measure in arbitrary normal coordinates for
    2.10.30, p. 195, from the block law
    and orthogonal invariance of 2.7.16(1), p. 135. *)
Theorem euclidean_normal_block_pushforward :
  measure_pushforward F (Leb (n+1))=product_measure ha hb.
Proof.
have hg : is_orthogonal_map (@euclidean_inner_product R (n+1))
    (@euclidean_inner_product R (n+1)) g.
  exact (orthogonal_inverse (normal_chart_orthogonal_law hD)
    (normal_chart_backward_inverse_law hD)).
apply: funext=> A.
change (Leb (n+1) (g @^-1` ((@euclidean_block_split R n 1) @^-1` A))=
  product_measure ha hb A).
rewrite (@euclidean_orthogonal_pushforward R (n+1) g hg).
exact (congr1 (fun mu=>mu A) (@euclidean_block_measure R n 1)).
Qed.

(** Source for [euclidean_normal_block_section_length]: direct scalar
    interpretation of the inner section measure in the Fubini argument of
    2.10.30, p. 195 *)
Lemma euclidean_normal_block_section_length (S : set (E (n+1))) (p : E n) :
  Leb 1 (product_vertical_section (H @^-1` S) p)=
    lebesgue_scalar_measure (normal_scalar_section u S (H (p,0))).
Proof.
rewrite /euclidean_lebesgue_measure positive_euclidean_lebesgue_first /measure_pushforward.
rewrite (@euclidean_normal_block_scalar_section R n D u hD S p); reflexivity.
Qed.

(** Source for [euclidean_normal_section_integral]: supporting
    normal-section Fubini identity used for volume
    equality in 2.10.30, p. 195. Measurability
    is retained explicitly, while sigma finiteness of
    the Euclidean factors is an established theorem. *)
Theorem euclidean_normal_section_integral (S : set (E (n+1))) :
  measure_measurable (Leb (n+1)) S ->
  is_measure_integral (Leb n)
    (partial_function_total (fun p=>lebesgue_scalar_measure (normal_scalar_section u S (H (p,0)))))
    (Leb (n+1) S).
Proof.
move=> hS.
pose K := H @^-1` S.
have hpre : F @^-1` K=S.
  apply/seteqP; split=> x;
    change (S (H (F x))->S x) || change (S x->S (H (F x)));
    by rewrite (@euclidean_normal_block_splitK R n D u hD x).
have hK : measure_measurable (product_measure ha hb) K.
  rewrite -euclidean_normal_block_pushforward.
  apply: pushforward_measurable_from_preimage; by rewrite hpre.
have hKc : measure_countably_measurable (product_measure ha hb) K.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb) hK (subsetT K)).
  exact: product_whole_countably_measurable (euclidean_lebesgue_countably_measurable R n)
    (euclidean_lebesgue_countably_measurable R 1).
have hi := (@product_set_fubini R [the choiceType of E n] [the choiceType of E 1]
  (Leb n) (Leb 1) ha hb K hKc).2.2.1.
have hmass : product_measure ha hb K=Leb (n+1) S.
  by rewrite -euclidean_normal_block_pushforward /measure_pushforward hpre.
have hf : (fun p=>Leb 1 (product_vertical_section K p))=
    (fun p=>lebesgue_scalar_measure (normal_scalar_section u S (H (p,0)))).
  apply: funext=> p; exact: euclidean_normal_block_section_length.
by rewrite hmass hf in hi.
Qed.
End NormalMeasure.
