(** Federer (1969), 3.2.5(1), pp. 244–245:
    a target Hausdorff-measurable weight pulls back measurably
    on the actual positive-Jacobian locus, using the inverse
    Lipschitz pieces and the completed Borel sigma algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  LipschitzUP NormMetricScaleContinuity EuclideanLipschitzClassZero InjectiveDifferentialPieceUP
  InjectiveDifferentialCover InnerOwnNormTopology BorelAreaSelection PositiveJacobianImageNull
  LipschitzMeasurableImages InjectivePieceNullPreimage CompletedBorelRelativePreimage
  MeasureUP MeasureSplit MeasureFiniteClosure MeasureCountableClosure BorelRegularMeasureUP
  TopologicalBorel BorelFunctionBasic HausdorffMeasure HausdorffClosedCoverAgreement
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasurableRelativeZeroExtension
  MeasureAlmostBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_jacobian_relative_preimage_measurable]:
    the completed-measurability step for the characteristic
    functions in Federer 3.2.5(1), p. 245. Only the
    represented image is countably Hausdorff measurable. *)
Theorem positive_jacobian_relative_preimage_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) T:
  is_metric_lipschitz setT f ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) T ->
  measure_measurable (@euclidean_lebesgue_measure R m)
    (positive_euclidean_jacobian_locus f `&` (f @^-1` T)).
Proof.
move=>hLip hT.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose beta:=@hausdorff_measure R Y m.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R Y m.
have hMB B:@borel_set [the topologicalType of X] B -> measure_measurable mu B.
  move=>hB; exact (@borel_regular_borel_measurable R X mu hm
    (euclidean_lebesgue_borel_regular R m) B hB).
have [M [hM hBound]]:=hLip.
have hCont:continuous f.
  apply:(@metric_fixed_lipschitz_continuous R X Y f M (ltW hM)).
  by move=>x y; exact (hBound.2 x y I I).
have [G hG]:=injective_differential_borel_cover_exists
  (euclidean_lipschitz_norm_class_zero hLip) (ltr1n R 2).
have hPre E:G E -> measure_measurable mu (E `&` (f @^-1` T)).
  move=>hE.
  have hEB:@borel_set [the topologicalType of X] E:=
    (inner_own_norm_borel_iff (@euclidean_inner_productP R m) E).2 (hG.2.2 E hE).1.
  have hIm:=euclidean_lipschitz_countably_measurable_image hLip (hMB E hEB).
  apply:(@completed_borel_relative_preimage R X Y mu beta hm hb
    (@hausdorff_measure_borel_regular R Y m) f E hMB (continuous_borel_function hCont) hEB hIm _ T hT).
  move=>N hN; exact (injective_differential_piece_null_preimage (hG.2.2 E hE) hN).
have hEq:positive_euclidean_jacobian_locus f `&` (f @^-1` T)=
    \bigcup_(E in G) (E `&` (f @^-1` T)).
  rewrite positive_jacobian_injective_locus -hG.2.1.
  apply/seteqP; split=>x.
  - move=>[[E hE hx] hTx]; exists E=>//; by split.
  - move=>[E hE [hx hTx]]; split=>//; by exists E.
rewrite hEq; exact (measure_measurable_countable_union hm hG.1 hPre).
Qed.

(** Source for [positive_jacobian_pullback_measurable]: the zero
    modification used in the characteristic approximation for
    Federer 3.2.5(1), p. 245. The original target weight
    is total, while the zero-extension object uses only its
    opaque graph laws. *)
Theorem positive_jacobian_pullback_measurable (R:realType) m n (Z:topologicalType) (zero:Z)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (g:R_n R n->Z):
  is_metric_lipschitz setT f ->
  is_measure_measurable_function
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) (partial_function_total g) ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (partial_function_zero_extension zero (positive_euclidean_jacobian_locus f)
      (partial_function_total (fun x=>g (f x)))).
Proof.
move=>hLip hg.
have hm:=euclidean_lebesgue_is_measure R m.
apply:(measurable_relative_zero_extension hm).
- exact (borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)
    (positive_jacobian_locus_borel hLip)).
- rewrite partial_function_total_domain; exact (measure_almost_everywhere_true hm).
- move=>U hU.
  exact (positive_jacobian_relative_preimage_measurable hLip (measurable_function_open_preimage hg hU)).
Qed.
