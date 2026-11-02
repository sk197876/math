(** Federer (1969), 3.2.5(1), p. 245: prove
    existence of a measurable auxiliary rank cutoff using
    only the existing opaque characteristic and zero-extension
    interfaces. No chosen cutoff is exposed globally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  ExtendedRealOrderTopology RealMetricBackground LipschitzUP HausdorffMeasure MeasureUP
  MeasurableFunctionUP MeasurableRealEmbedding MeasurableGraphEquivalence MeasurableZeroExtension
  CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionBasic PartialZeroExtension
  BorelAreaSelection PositiveJacobianPullbackMeasurable AreaRankWeightUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_area_rank_weight_exists]: supporting
    measurable-existence claim in the nonnegative approximation
    proof of Federer 3.2.5(1), p. 245. The source
    set may be merely Lebesgue measurable. *)
Theorem measurable_area_rank_weight_exists (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:inner_metric_space (@euclidean_inner_productP R n)->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_measurable_function (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total g) ->
  exists u,is_area_rank_weight f A g u /\
    is_measure_measurable_function (@euclidean_lebesgue_measure R m) (partial_function_total u).
Proof.
move=>hLip hA hg.
pose P:=positive_euclidean_jacobian_locus f.
pose a:=@CharacteristicFunction.value R (R_n R m) A.
pose p:=@CharacteristicFunction.value R (R_n R m) P.
have ha:is_characteristic_function A a:=@CharacteristicFunction.laws R (R_n R m) A.
have hp:is_characteristic_function P p:=@CharacteristicFunction.laws R (R_n R m) P.
pose u x:=((a x * p x * g (f x))%R%:E:extended_real_line R).
have hU:is_area_rank_weight f A g u.
  constructor.
  - move=>x hAx hPx; by rewrite /u (characteristic_on_set ha hAx) (characteristic_on_set hp hPx) !mul1r.
  - move=>x hNot; case:(pselect (A x))=>hAx.
    + have hPx:~P x by move=>h; apply:hNot; by split.
      by rewrite /u (characteristic_off_set hp hPx) mulr0 mul0r.
    + by rewrite /u (characteristic_off_set ha hAx) !mul0r.
have hG:=measurable_total_real_embedding (@hausdorff_measure_is_measure R _ m) hg.
have hP:=positive_jacobian_pullback_measurable (0:extended_real_line R) hLip hG.
have hDouble:=@measurable_zero_extension R [the choiceType of (R_n R m : Type)] (extended_real_line R)
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) 0 A
  (partial_function_zero_extension (0:extended_real_line R) P
    (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))) hA hP.
exists u; split=>//.
exact (@measurable_function_graph_equivalent R _ (extended_real_line R) _ _
  (partial_function_total u) (area_rank_weight_graph hU) hDouble).
Qed.
