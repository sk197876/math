(** Federer (1969), 4.1.18, p. 374: original
    compact-kernel smoothing commutes with constant-coefficient
    first-order operators, in particular exterior differentiation.
    Reuse the full input differential theorem of 4.1.2,
    without whole operator-space separability.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  NormDifferentialUP NormClassOneUP NormRegularity NormHigherDifferentialUnique
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP
  SmoothHigherDerivativeRegularity SmoothFirstOrderUP SmoothFirstOrderSealed
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  SmoothSmoothingFamilyUP SmoothingConvolutionUP SmoothingInputHigherDifferential
  ContinuousConvolutionLinearImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothSmoothingFirstOrderCommutation.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Variables Y Z:lmodType R.
Variables (NY:Y->R) (NZ:Z->R).
Hypotheses (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Hypothesis hZ:is_complete_metric_space (real_norm_metric_space hNZ).
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypotheses (hE:is_smooth_function_space hNX hNY Full ev)
  (hF:is_smooth_function_space hNX hNZ Full fv).
Local Notation Jet:=(fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation je:=(fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation JN:=(fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hJet:=(fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Jet k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY Full E ev D.
Variable L:Hom (Jet 1%N) Z.
Hypothesis hL:norm_bounded_linear (JN 1%N) NZ L.
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variables (PY:R->Hom E E) (PZ:R->Hom F F).
Hypotheses (hPY:is_smooth_smoothing_family hNY ev family PY)
  (hPZ:is_smooth_smoothing_family hNZ fv family PZ).
Local Notation Op:=(@SmoothFirstOrder.operator R X Y Z NX NY NZ hNX hNY hNZ
  Full E F ev fv hE hF D hD L hL).

(** Source for [smooth_smoothing_first_differential_convolution]:
    the actual full first differential commutes with
    the original regularisation, from 4.1.2, p. 347,
    supporting 4.1.18, p. 374. *)
Lemma smooth_smoothing_first_differential_convolution epsilon:
  0<epsilon ->forall omega:E,
  is_smoothing_convolution (continuous_multilinear_norm_is_norm hNY (hJet 1%N))
    (family epsilon) (fun x=>@D 1%N x omega)
    (fun x=>@D 1%N x (PY epsilon omega)).
Proof.
move=>he omega.
have [DF [DG [hDF [hDG hConv]]]]:=@smoothing_input_higher_differential_exists
  R n Y NY hNY hY hSep phi hPhi family hFamily epsilon he 1%N
  (ev omega) (ev (PY epsilon omega))
  (smooth_function_evaluation_smooth hE omega 1%N) (@hPY epsilon he omega).
have hFEqual:DF=(fun x=>@D 1%N x omega).
  apply:funext=>x.
  exact:(norm_higher_differential_unique hNX hNY hJet (hDF x)
    (@smooth_derivative_exact R X Y NX NY hNX hNY Full E ev D hD
      1%N omega x Logic.I)).
have hGEqual:DG=(fun x=>@D 1%N x (PY epsilon omega)).
  apply:funext=>x.
  exact:(norm_higher_differential_unique hNX hNY hJet (hDG x)
    (@smooth_derivative_exact R X Y NX NY hNX hNY Full E ev D hD
      1%N (PY epsilon omega) x Logic.I)).
by rewrite -hFEqual -hGEqual.
Qed.

(** Source for [smooth_smoothing_first_order_commutation]:
    the original constant-coefficient operator commutes
    with smoothing, supporting boundary commutation and
    both form homotopy identities of 4.1.18, p. 374.
    The result uses only the independently specified
    smoothing and first-order operator laws. *)
Theorem smooth_smoothing_first_order_commutation epsilon:
  0<epsilon ->forall omega:E,
    Op (PY epsilon omega)=PZ epsilon (Op omega).
Proof.
move=>he omega.
pose hJN:=continuous_multilinear_norm_is_norm hNY (hJet 1%N).
have hDF:norm_class_zero NX (JN 1%N) Full (fun x=>@D 1%N x omega).
  exact:norm_class_continuous
    (@smooth_higher_derivative_field_regular R X Y NX NY hNX hNY Full
      E ev hE 1%N D hD omega 0%N).
have hConv:=@continuous_convolution_linear_image R n (Jet 1%N) Z (JN 1%N) NZ
  hJN hNZ hZ (fun x=>@D 1%N x omega) (fun x=>@D 1%N x (PY epsilon omega))
  (family epsilon) epsilon hDF
  (@smoothing_dilation_smooth R n phi hPhi family hFamily epsilon he)
  (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily epsilon he)
  L hL (@smooth_smoothing_first_differential_convolution epsilon he omega).
have hValue theta:fv (Op theta)=(fun x=>L (@D 1%N x theta)).
  apply:funext=>x.
  exact:(@SmoothFirstOrder.laws R X Y Z NX NY NZ hNX hNY hNZ
    Full E F ev fv hE hF D hD L hL theta x Logic.I).
rewrite -(hValue omega) -(hValue (PY epsilon omega)) in hConv.
have hEqual:=@smoothing_convolution_unique R n Z NZ hNZ (family epsilon)
  (fv (Op omega)) (fv (Op (PY epsilon omega))) (fv (PZ epsilon (Op omega)))
  hConv (@hPZ epsilon he (Op omega)).
apply:(smooth_function_extensional hF)=>x _.
exact:(congr1 (fun f:X->Z=>f x) hEqual).
Qed.
End SmoothSmoothingFirstOrderCommutation.
