(** Federer (1969), 4.1.2, p. 347: the
    class-i input and smoothed output have actual
    multiindex derivative fields, whose convolution values
    satisfy the original commutation formula. Derivative
    existence is discharged, not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherMultiPartialUP NormClassHigherUP
  ContinuousFieldLocalIntegrability SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP CompactSmoothConvolutionSmoothness SmoothingInputMultiPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothingInputMultiPartialExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable e:R.
Hypothesis he:0<e.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).

(** Source for [smoothing_input_multi_partial_exists]: the complete
    class-i multiindex commutation assertion of Federer
    4.1.2, p. 347. Actual input
    and output derivative fields and their actual
    convolution integral values are all proved to exist. *)
Theorem smoothing_input_multi_partial_exists k (alpha:symmetric_indices n k) (f g:X->Y):
  norm_class hN hNY (fun _=>True) f k ->
  is_smoothing_convolution hNY (family e) f g ->
  exists theta q:X->Y,
    (forall a,has_norm_multi_partial N ez ZN (fun _=>True) f alpha a (theta a)) /\
    (forall a,has_norm_multi_partial N ez ZN (fun _=>True) g alpha a (q a)) /\
    is_smoothing_convolution hNY (family e) theta q.
Proof.
move=>hClass hConv.
have hLocal:=@continuous_field_locally_norm_integrable R n Y NY hNY f (norm_class_continuous hClass).
have hKernel:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hOff z:e<N z ->family e z=0.
  exact:(@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he z).
have hG:=@compact_smooth_convolution_smooth R n Y NY hNY hY hSep f hLocal
  (family e) e g hKernel hOff hConv.
have [_ [DF [hDF _]]]:=hClass.
have [_ [DG [hDG _]]]:=hG k.
pose theta:=fun a=>@ez k (norm_multi_partial_arguments R alpha) (DF a).
pose q:=fun a=>@ez k (norm_multi_partial_arguments R alpha) (DG a).
have hTheta a:has_norm_multi_partial N ez ZN (fun _=>True) f alpha a (theta a).
  exists (DF a); split; first exact:(@hDF a Logic.I).
  reflexivity.
have hQ a:has_norm_multi_partial N ez ZN (fun _=>True) g alpha a (q a).
  exists (DG a); split; first exact:(@hDG a Logic.I).
  reflexivity.
exists theta,q; split=>//; split=>//.
exact:(@smoothing_input_multi_partial R n Y NY hNY hY hSep phi hPhi family hFamily e he
  k alpha f g theta q hClass hConv hTheta hQ).
Qed.
End SmoothingInputMultiPartialExistence.
