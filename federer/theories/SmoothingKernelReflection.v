(** Federer (1969), 4.1.18, pp. 374–375: current
    smoothing averages test translations with the reflected
    weight. To obtain ordinary smoothing of a density
    field, reflect the kernel explicitly. Reflection
    preserves every original 4.1.2 kernel law; no
    symmetry assumption is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormRegularityLinearMaps NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CompactSupportFunctionUP SmoothingKernelUP
  SmoothingDilationUP EuclideanLebesgueDimensions EuclideanReflectionTranslation
  MeasureUP MeasurePushforward MeasureIntegralUP SummableRealFunctionUP InvariantRealIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothingKernelReflection.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Local Notation reflected:=(fun x:X=>phi (-x)).

(** Source for [smoothing_reflected_kernel_laws]: the
    reflected original kernel again satisfies all
    positivity, smoothness, compact-support and unit-mass
    laws of 4.1.2, supporting the distinction between
    current and field convolution in 4.1.18, p. 375. *)
Theorem smoothing_reflected_kernel_laws:is_smoothing_kernel reflected.
Proof.
pose L:Hom X X:= -(hom_of_linear (@linear_id R X)).
have hBound:norm_bounded_linear NX NX L.
  exists 1;split;first exact:ler01.
  by move=>x;change (is_true (NX (-x)<=1*NX x));rewrite inner_normN mul1r.
have hNeg:continuous (fun x:XT=>(-x:XT)).
  exact:(@norm_bounded_linear_continuous R X X NX NX hNX hNX L hBound).
pose K:set XT:=(fun x:XT=>-x) @` @real_function_support R XT phi.
have hK:compact K.
  exact:continuous_compact (continuous_subspaceT hNeg) (smoothing_kernel_support_compact hPhi).
have hClosed:closed K:=compact_closed (@metric_hausdorff R XT) hK.
have hOff:forall x,~K x->reflected x=0.
  move=>x hx;apply:(@real_function_zero_off_support R XT phi (-x))=>hSupport.
  apply:hx;exists (-x);first exact:hSupport.
  exact:opprK.
have hSupport:@real_function_support R XT reflected `<=` K.
  exact:real_function_support_in_closed_set hClosed hOff.
constructor.
- move=>k.
  exact:(@norm_class_precompose_linear R X X R^o NX NX (fun t:R^o=>`|t|)
    hNX hNX (@scalar_absolute_value_norm R) (fun _=>True) phi L k hBound
    (smoothing_kernel_smooth hPhi k)).
- by move=>x;exact:smoothing_kernel_nonnegative hPhi (-x).
- exact:(@subclosed_compact XT (@real_function_support R XT reflected) K
    (@real_function_support_closed R XT reflected) hK hSupport).
- move=>x hx;have[y hy hValue]:=hSupport x hx.
  rewrite -hValue.
  change (is_true (NX (-y)<1)).
  rewrite inner_normN.
  exact:(@smoothing_kernel_support_unit_ball R n phi hPhi y hy).
- have hReflection:measure_pushforward (fun x:X=>-x) (@euclidean_lebesgue_measure R n)=
      @euclidean_lebesgue_measure R n.
    have h:=@euclidean_reflection_translation_measure R n 0.
    have hFunction:(fun x:X=>0-x)=(fun x=>-x).
      by apply:funext=>x;rewrite sub0r.
    by rewrite hFunction in h.
  exact:(@invariant_real_total_integral R X (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (fun x:X=>-x) phi 1
    (@oppr_inj X) hReflection (smoothing_kernel_integral_one hPhi)).
Qed.

(** Source for [smoothing_reflected_dilation_laws]:
    reflecting the actual family preserves the original
    positive-scale dilation formula, supporting ordinary
    field convolution in Federer 4.1.18, p. 375. *)
Theorem smoothing_reflected_dilation_laws (family:R->X->R):
  is_smoothing_dilation phi family ->
  is_smoothing_dilation reflected (fun epsilon x=>family epsilon (-x)).
Proof.
move=>hFamily epsilon hEpsilon x.
by rewrite (hFamily epsilon hEpsilon (-x)) scalerN.
Qed.
End SmoothingKernelReflection.
