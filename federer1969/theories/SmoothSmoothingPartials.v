(** Federer (1969), 4.1.2, p. 347: the
    original coordinate derivative fields of smooth
    functions are continuous and commute with
    smoothing. All spaces and derivative operators
    are supplied through their independent public laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed ContinuousMultilinearEvaluationBound
  NormClassOneUP NormHigherMultiPartialUP NormRegularityLinearMaps
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothHigherDerivativeRegularity
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP SmoothSmoothingFamilyUP SmoothingInputMultiPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothSmoothingPartials.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.

(** Source for [smooth_multi_partial_field_continuous]: every
    fixed original multiindex derivative of a smooth
    function is continuous, supporting the seminorm
    convergence in Federer 4.1.2, p. 347. *)
Theorem smooth_multi_partial_field_continuous k (alpha:symmetric_indices n k) f:
  norm_class_zero N NY (fun _=>True)
    (fun x=>@ez k (norm_multi_partial_arguments R alpha) (@D k x f)).
Proof.
pose hNk:=continuous_multilinear_norm_is_norm hNY (hZ k).
have hField:=@smooth_higher_derivative_field_regular R X Y N NY hN hNY (fun _=>True)
  E ev hE k D hD f 0%N.
have hValue:=@norm_class_postcompose_linear R X (Z k) Y N (@ZN k) NY hN hNk hNY
  (fun _=>True) (fun x=>@D k x f) (@ez k (norm_multi_partial_arguments R alpha)) 0%N
  (continuous_multilinear_evaluation_bounded hN (hZ k) (norm_multi_partial_arguments R alpha)) hField.
exact:norm_class_continuous hValue.
Qed.

Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.

(** Source for [smooth_smoothing_multi_partial_convolution]: the
    exact original derivative fields of P_epsilon f
    are convolutions of those of f, supporting
    smooth convergence in Federer 4.1.2, p. 347. *)
Theorem smooth_smoothing_multi_partial_convolution k (alpha:symmetric_indices n k) f e:
  0<e ->is_smoothing_convolution hNY (family e)
    (fun x=>@ez k (norm_multi_partial_arguments R alpha) (@D k x f))
    (fun x=>@ez k (norm_multi_partial_arguments R alpha) (@D k x (P e f))).
Proof.
move=>he.
apply:(@smoothing_input_multi_partial R n Y NY hNY hY hSep phi hPhi family hFamily e he
  k alpha (ev f) (ev (P e f)) _ _ (smooth_function_evaluation_smooth hE f k) (@hP e he f)).
- move=>a; exists (@D k a f); split.
  + exact:(@smooth_derivative_exact R X Y N NY hN hNY (fun _=>True) E ev D hD k f a Logic.I).
  + reflexivity.
- move=>a; exists (@D k a (P e f)); split.
  + exact:(@smooth_derivative_exact R X Y N NY hN hNY (fun _=>True) E ev D hD k (P e f) a Logic.I).
  + reflexivity.
Qed.
End SmoothSmoothingPartials.
