(** Federer (1969), 4.1.2, p. 347: the full
    multilinear-valued identity D^i(Phi*f)=Phi*D^i f.
    The original coordinate reconstruction turns the proved
    partial identities into the actual operator-valued integral.
    No separability of the entire operator space is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormClassOneUP NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed ContinuousMultilinearBanach
  ContinuousMultilinearEvaluationBound NormHigherDifferentialUP NormHigherMultiPartialUP NormClassHigherUP
  NormClassZeroPostcompose NormHigherCoordinateReconstruction
  PartialFunctionUP PartialFunctionBasic MeasureVectorIntegralUP EuclideanLebesgueDimensions
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothingConvolutionUP ContinuousFieldLocalIntegrability CompactSmoothConvolutionSmoothness SmoothingInputMultiPartial
  ContinuousCompactConvolution TotalVectorIntegralLinearImage TotalVectorIntegralFiniteSum TotalVectorIntegralArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingInputHigherDifferential.
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
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).

(** Source for [smoothing_input_higher_differential_exists]:
    the exact original class-i identity in Federer 4.1.2,
    p. 347. Both full differentials exist
    and their actual Banach-valued convolution is proved. *)
Theorem smoothing_input_higher_differential_exists k (f g:X->Y):
  norm_class hN hNY (fun _=>True) f k ->
  is_smoothing_convolution hNY (family e) f g ->
  exists DF DG:X->Z k,
    (forall a,has_norm_higher_differential N ez ZN (fun _=>True) f k a (DF a)) /\
    (forall a,has_norm_higher_differential N ez ZN (fun _=>True) g k a (DG a)) /\
    is_smoothing_convolution (continuous_multilinear_norm_is_norm hNY (hZ k)) (family e) DF DG.
Proof.
move=>hF hConv.
have hLocal:=@continuous_field_locally_norm_integrable R n Y NY hNY f (norm_class_continuous hF).
have hKernel:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
have hOff z:e<N z ->family e z=0.
  exact:(@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he z).
have hG:=@compact_smooth_convolution_smooth R n Y NY hNY hY hSep f hLocal
  (family e) e g hKernel hOff hConv.
have[_ [DF [hDF hDFCont]]]:=hF.
have[_ [DG [hDG hDGCont]]]:=hG k.
pose hNk:=continuous_multilinear_norm_is_norm hNY (hZ k).
have hComplete:=@continuous_multilinear_complete_general R k X Y (Z k) N NY hN hNY
  (@ez k) (@ZN k) (hZ k) hY.
have[L [hL hReconstruction]]:=@norm_higher_coordinate_reconstruction_exists R n Y NY hNY Z ez ZN hZ k.
pose theta alpha a:=@ez k (norm_multi_partial_arguments R alpha) (DF a).
pose q alpha a:=@ez k (norm_multi_partial_arguments R alpha) (DG a).
have hTheta alpha a:has_norm_multi_partial N ez ZN (fun _=>True) f alpha a (theta alpha a).
  exists (DF a); split; first exact:(@hDF a Logic.I).
  reflexivity.
have hQ alpha a:has_norm_multi_partial N ez ZN (fun _=>True) g alpha a (q alpha a).
  exists (DG a); split; first exact:(@hDG a Logic.I).
  reflexivity.
have hPartial alpha:is_smoothing_convolution hNY (family e) (theta alpha) (q alpha).
  exact:(@smoothing_input_multi_partial R n Y NY hNY hY hSep phi hPhi family hFamily e he
    k alpha f g _ _ hF hConv (hTheta alpha) (hQ alpha)).
have hThetaCont alpha:norm_class_zero N NY (fun _=>True) (theta alpha).
  exact:(@norm_class_zero_postcompose R X (Z k) Y N (@ZN k) NY hNk
    (fun _=>True) DF (@ez k (norm_multi_partial_arguments R alpha)) hDFCont
    (continuous_multilinear_evaluation_bounded hN (hZ k) (norm_multi_partial_arguments R alpha))).
exists DF,DG; split; first by move=>a; exact:(@hDF a Logic.I).
split; first by move=>a; exact:(@hDG a Logic.I).
move=>x.
have hImage alpha:is_measure_vector_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun z=>(L alpha (family e (x-z)*:theta alpha z):
      real_norm_metric_space hNk))) (L alpha (q alpha x)).
  have hCont:=@norm_class_zero_postcompose R X Y (Z k) N NY (@ZN k) hNY
    (fun _=>True) (theta alpha) (L alpha) (hThetaCont alpha) (hL alpha).
  have[w hw]:=@continuous_compact_convolution_at_exists R n (Z k) (@ZN k) hNk hComplete
    (fun z=>L alpha (theta alpha z)) hCont (family e) hKernel e hOff x.
  have hEq:(fun z=>L alpha (family e (x-z)*:theta alpha z))=
      (fun z=>family e (x-z)*:L alpha (theta alpha z)).
    apply:funext=>z; by rewrite linearZ.
  rewrite -hEq in hw.
  exact:(@total_vector_integral_linear_image R X Y (Z k) NY (@ZN k) hNY hNk
    (@euclidean_lebesgue_measure R n) (L alpha) (fun z=>family e (x-z)*:theta alpha z)
    (q alpha x) (hL alpha) hw.1 (hPartial alpha x)).
have hSum:=@total_vector_integral_finite_sum R X (Z k) (@ZN k) hNk
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (symmetric_indices n k) (fun alpha z=>L alpha (family e (x-z)*:theta alpha z))
  (fun alpha=>L alpha (q alpha x)) hImage.
have hOutput:DG x=\sum_alpha L alpha (q alpha x).
  exact:(hReconstruction (fun _=>True) g x (DG x) (q^~x) (@hDG x Logic.I) (fun alpha=>hQ alpha x)).
rewrite -hOutput in hSum.
apply:(@measure_vector_integral_graph_equivalent R X (Z k) (@ZN k) hNk
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) _ _ _ _ hSum)=>z v.
have hInput:DF z=\sum_alpha L alpha (theta alpha z).
  exact:(hReconstruction (fun _=>True) f z (DF z) (theta^~z) (@hDF z Logic.I)
    (fun alpha=>hTheta alpha z)).
have hValue:(\sum_alpha L alpha (family e (x-z)*:theta alpha z))=family e (x-z)*:DF z.
  rewrite hInput scaler_sumr; apply:eq_bigr=>alpha _; by rewrite linearZ.
change ((\sum_alpha L alpha (family e (x-z)*:theta alpha z))=v <->
  family e (x-z)*:DF z=v).
by rewrite hValue.
Qed.
End SmoothingInputHigherDifferential.
