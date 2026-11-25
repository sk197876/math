(** Federer (1969), 4.1.5, p. 350: the
    original continuous-tail decomposition and both actual
    convolution inequalities imply
    T(w)<=||S||(||w||)+eta ||S||(g).
    Every convolution, support and limit premise is
    discharged for the actual test space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FunctionLatticeUP CompactSupportFunctionUP CompactContinuousVectorFields CompactContinuousDomainFields
  CompactContinuousDomainAlgebra CompactNormTailUP CompactNormTailExistence CompactNormTailFieldLaws
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP
  CompactUniformApproximationUP CompactContinuousConvolutionApproximation NormTailSmoothingBound PlateauSmoothingBound
  DistributionVariationUP DistributionContinuousExtensionUP DistributionExtensionApproximationBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionNormTailEstimate.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation Q := (@compact_continuous_domain_fields R XT U Y NY hNY).
Variable S:Hom DT R^o.
Variable T:(X->Y)->R.
Hypothesis hT:@is_distribution_continuous_extension R XT U Y NY hNY DT values S T.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [distribution_norm_tail_estimate]: the last
    displayed estimate of Federer 4.1.5, p. 350,
    proved with the original h w and w-h w and
    their actual small-scale convolutions. *)
Theorem distribution_norm_tail_estimate w b (g:X->R) c (W:set XT):
  Q w ->open W ->
  @real_function_support R XT (fun x=>NY (w x)) `<=` W ->
  (forall x,0<=g x) ->(forall x,W x ->g x= 1) ->
  is_distribution_variation_value NY values S (fun x=>NY (w x)) b%:E ->
  is_distribution_variation_value NY values S g c%:E ->
  forall eta:R,0<eta ->T w<=b+eta*c.
Proof.
move=>hw hW hKW hG hOne hGaugeW hGaugeG eta hEta.
have[h hH]:=@compact_norm_tail_cutoff_exists R XT Y NY hNY w eta hw.1 hEta.
pose u:=fun x:X=>h x*:w x.
pose v:=fun x:X=>w x-h x*:w x.
have hu:Q u:=@compact_norm_tail_field_inside R XT Y NY hNY w eta h hH U hw.
have hv:Q v:=@compact_continuous_domain_subtract R XT U Y NY hNY w u hw hu.
have[Pu [hAPu [ru [hru hConvu]]]]:=@compact_continuous_convolution_test_approximation
  R n Y NY hNY hY U hU E ev hE phi hPhi family hFamily u hu.
have[Pv [hAPv [rv [hrv hConvv]]]]:=@compact_continuous_convolution_test_approximation
  R n Y NY hNY hY U hU E ev hE phi hPhi family hFamily v hv.
have hNormMajorant:@positive_function_lattice R X (@compactly_supported_continuous_functions R XT)
    (fun x=>NY (w x)).
  split; first exact:compact_continuous_vector_field_norm hw.1.
  move=>x; exact:(real_seminorm_nonnegative hNY.1 (w x)).
have hTailNorm:forall x,NY (u x)=Num.max (NY (w x)-eta) 0.
  exact:(@compact_norm_tail_field_norm R XT Y NY hNY w eta h hH).
have[C0 [hC0 [hCU0 [r0 [hr0 [hOff0 hUniform]]]]]]:=hAPu.
have[du [hdu [_ hBoundU]]]:=@norm_tail_smoothing_pointwise_bound R n Y NY hNY phi hPhi family hFamily
  (fun x=>NY (w x)) eta u (fun e=>value (Pu e)) ru
  hNormMajorant hEta hru hTailNorm hConvu hUniform.
have hUpperU:T u<=b.
  apply:(@distribution_extension_approximation_upper R XT U Y NY hNY DT values S T hT u Pu
    (fun x=>NY (w x)) b hu hAPu hGaugeW).
  by exists du.
have hOffV:forall x,~@real_function_support R XT (fun x=>NY (w x)) x ->v x=0.
  move=>x hx; rewrite /v (@compact_continuous_vector_zero_off_norm_support R XT Y NY hNY w x hx).
  by rewrite scaler0 subrr.
have hBoundV:forall x,NY (v x)<=eta.
  exact:(@compact_norm_tail_remainder_bound R XT Y NY hNY w eta h hH hEta).
have[dv [hdv [_ hPointwiseV]]]:=@plateau_smoothing_pointwise_bound R n Y NY hNY phi hPhi family hFamily
  (@real_function_support R XT (fun x=>NY (w x))) W g v (fun e=>value (Pv e)) eta rv
  hw.1.2 hW hKW hG hOne (ltW hEta) hrv hOffV hBoundV hConvv.
have hAbsoluteV:`|T v|<=eta*c.
  apply:(@distribution_extension_approximation_scaled_bound R XT U Y NY hNY DT values S T hT
    v Pv g c eta hv hAPv hGaugeG hEta).
  by exists dv.
have hSum:(fun x=>u x+v x)=w.
  apply:funext=>x; by rewrite /u /v addrC subrK.
have hLinear:=@distribution_extension_add R XT U Y NY hNY DT values S T hT u v hu hv.
rewrite hSum in hLinear.
rewrite hLinear; exact:lerD hUpperU (le_trans (ler_norm _) hAbsoluteV).
Qed.
End DistributionNormTailEstimate.
