(** Federer (1969), 4.1.2, p. 347: smoothing
    converges uniformly on compact sets in every
    full derivative norm. Original finite coordinate
    reconstruction converts the previously proved
    approximation of each coordinate partial into this bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherMultiPartialUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP FiniteCommonRadius
  HigherDifferentialFinitePartialBound SmoothingKernelUP SmoothingDilationUP SmoothSmoothingFamilyUP
  SmoothSmoothingPartials SmoothingLocallyUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothSmoothingDerivativeUniform.
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
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y N NY hN hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y N NY hN hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.

(** Source for [smooth_smoothing_derivative_uniform]: the
    compact-uniform convergence of every derivative required
    by the original E and D convergence assertions,
    Federer 4.1.2, p. 347. No
    replacement norm or finite target dimension is used. *)
Theorem smooth_smoothing_derivative_uniform k f
    (K:smooth_compact_set hN (fun _=>True)) (eta:R):
  0<eta ->exists d:R,0<d /\ forall e:R,0<e ->e<d ->
    forall a,smooth_compact_carrier K a ->
      @ZN k (@D k a (P e f-f))<eta.
Proof.
move=>hEta.
have [M [hM hBound]]:=@norm_higher_differential_finite_partial_bound R n Y NY hNY Z ez ZN hZ k.
pose r:=(eta/2)/M.
have hR:0<r by rewrite /r !divr_gt0 // ltr0n.
have hEach (alpha:symmetric_indices n k):exists d:R,0<d /\ forall e:R,e<d ->0<e ->
    forall a,smooth_compact_carrier K a ->
      NY (@ez k (norm_multi_partial_arguments R alpha) (@D k a (P e f))-
        @ez k (norm_multi_partial_arguments R alpha) (@D k a f))<r.
  have hCont:=@smooth_multi_partial_field_continuous R n Y NY hNY E ev hE D hD k alpha f.
  have hConv e (he:0<e):=
    @smooth_smoothing_multi_partial_convolution R n Y NY hNY E ev hE D hD hY hSep
      phi hPhi family hFamily P hP k alpha f e he.
  have [d [hd hUniform]]:=@smoothing_continuous_locally_uniform R n Y NY hNY hSep
    phi hPhi family hFamily
    (fun x=>@ez k (norm_multi_partial_arguments R alpha) (@D k x f))
    (fun e x=>@ez k (norm_multi_partial_arguments R alpha) (@D k x (P e f)))
    hConv hCont K r hR.
  exists d; split=>// e he hPositive a ha; exact:(hUniform e hPositive he a ha).
have [d [hd hUniform]]:=@finite_common_radius R (Finite.clone (symmetric_indices n k) _) R
  (fun e=>e) (fun alpha e=>0<e ->forall a,smooth_compact_carrier K a ->
    NY (@ez k (norm_multi_partial_arguments R alpha) (@D k a (P e f))-
      @ez k (norm_multi_partial_arguments R alpha) (@D k a f))<r) hEach.
exists d; split=>// e he hSmall a ha.
have hCoefficients alpha:NY (@ez k (norm_multi_partial_arguments R alpha) (@D k a (P e f-f)))<=r.
  rewrite !linearB.
  exact:ltW (hUniform alpha e hSmall he a ha).
have hActual:=@smooth_derivative_exact R X Y N NY hN hNY (fun _=>True) E ev D hD
  k (P e f-f) a Logic.I.
have hNorm:=hBound (fun _=>True) (ev (P e f-f)) a (@D k a (P e f-f)) r (ltW hR) hActual hCoefficients.
have hMr:M*r=eta/2 by rewrite /r mulrC divfK // gt_eqF.
rewrite hMr in hNorm.
apply:le_lt_trans hNorm _; lra.
Qed.
End SmoothSmoothingDerivativeUniform.
