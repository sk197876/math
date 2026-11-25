(** Federer (1969), 3.2.5(1), p. 245, in the
    Riemannian extension of 3.2.46, p. 282:
    prove measurable existence of the independently specified
    rank cutoff from actual completed positive-locus pullback.
    The auxiliary weight remains a local proof witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianLocalAreaSelection RiemannianPositiveWeightPullback RiemannianAreaRankWeightUP
  CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasurableFunctionUP MeasurableRealEmbedding MeasurableZeroExtension MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_riemannian_area_rank_weight_exists]:
    measurable cutoff existence in 3.2.5(1), p. 245,
    with actual original Riemannian objects in 3.2.46,
    p. 282. Source S need only be completed
    measurable, and target weight measurability suffices.
    No selected global cutoff or derivative field is added. *)
Theorem measurable_riemannian_area_rank_weight_exists (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) S (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total u) ->
  exists w, is_riemannian_area_rank_weight f S u w /\
    is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp) (partial_function_total w).
Proof.
move=> hLip hS hU.
pose X := [the choiceType of riemannian_metric_space hg].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
pose P := positive_riemannian_area_locus f.
pose a := @CharacteristicFunction.value R X S.
pose p := @CharacteristicFunction.value R X P.
have hA := @CharacteristicFunction.laws R X S.
have hP := @CharacteristicFunction.laws R X P.
pose w x : extended_real_line R := (a x * p x * u (f x))%R%:E.
have hW : is_riemannian_area_rank_weight f S u w.
  constructor.
  - move=> x hx hxP; by rewrite /w /a /p (characteristic_on_set hA hx) (characteristic_on_set hP hxP) !mul1r.
  - move=> x hNot; case: (pselect (S x))=> hx.
    + have hxP : ~ P x by move=> hxP; apply: hNot; by split.
      by rewrite /w /a /p (characteristic_off_set hP hxP) mulr0 mul0r.
    + by rewrite /w /a /p (characteristic_off_set hA hx) !mul0r.
have hEmbedded := measurable_total_real_embedding
  (@riemannian_hausdorff_is_measure R n B h hh m%:R hp) hU.
have hPullback := @riemannian_positive_area_weight_pullback R m n A B g h hg hh f hp
  (extended_real_line R) 0 (fun y=>((u y)%:E : extended_real_line R)) hLip hEmbedded.
have hDouble := @measurable_zero_extension R X (extended_real_line R) mu
  (@riemannian_hausdorff_is_measure R m A g hg m%:R hp) 0 S
  (partial_function_zero_extension (0 : extended_real_line R) P
    (partial_function_total (fun x=>((u (f x))%:E : extended_real_line R)))) hS hPullback.
exists w; split; first exact hW.
exact (@measurable_function_graph_equivalent R X (extended_real_line R) mu _
  (partial_function_total w) (riemannian_area_rank_weight_graph hW) hDouble).
Qed.
