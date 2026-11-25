(** Federer (1969), 4.1.5, p. 349: the original
    finite-gauge hypothesis supplies the actual scalar
    convolution limit for every compact continuous field.
    Common compact support and the existing localized
    cutoff discharge the Cauchy hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  CompleteMetricUP NormClassOneUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FiniteNormEquivalence FunctionLatticeUP CompactSupportFunctionUP CompactCutoffUP LocalizedCompactCutoffUP
  LocalizedCompactCutoff SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  SmoothingKernelUP SmoothingDilationUP SmoothingConvolutionUP CompactContinuousSmoothingTests
  DistributionVariationUP DistributionVariationCauchy PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionCompactContinuousLimit.
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
Local Notation support := (@smooth_function_support R X Y N hN U DT value).
Variable S:Hom DT R^o.
Hypothesis hFinite:forall f:X->R,
  @positive_function_lattice R X (@compactly_supported_continuous_functions R XT) f ->
  @real_function_support R XT f `<=` U ->
  exists b:R,is_distribution_variation_value NY values S f b%:E.
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.

(** Source for [distribution_compact_continuous_limit]:
    the existence of T(w)=lim S(Phi_e*w) asserted in
    Federer 4.1.5, p. 349, with actual tests on the
    arbitrary original open U. Only the original finite
    gauge, Banach completeness and compact support are used. *)
Theorem distribution_compact_continuous_limit
    (K:smooth_compact_set hN U) (w:X->Y):
  norm_class_zero N NY (fun _=>True) w ->
  (forall x,~smooth_compact_carrier K x ->w x=0) ->
  exists t:R,exists r:R,0<r /\ exists C:smooth_compact_set hN U,exists P:R->DT,
    (forall e:R,0<e ->e<r ->
      is_smoothing_convolution hNY (family e) w (value (P e)) /\
      support (P e) `<=` smooth_compact_carrier C) /\
    (forall eta:R,0<eta ->exists d:R,0<d /\ d<=r /\
      forall e:R,0<e ->e<d ->forall x,NY (value (P e) x-w x)<eta) /\
    positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) t.
Proof.
move=>hContinuous hOff.
have[r [hr [C [P [hP hApprox]]]]]:=@compact_continuous_smoothing_tests
  R n Y NY hNY hY U hU E ev hE phi hPhi family hFamily K w hContinuous hOff.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
pose g:=@localized_compact_cutoff R XT (smooth_compact_carrier C) U
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN)
  (smooth_compact_is_compact C) hOpen (smooth_compact_in_domain C).
have hG:=@localized_compact_cutoff_specification R XT (smooth_compact_carrier C) U
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN)
  (smooth_compact_is_compact C) hOpen (smooth_compact_in_domain C).
have hNonnegative:function_nonnegative g.
  move=>x; exact:(andP (compact_cutoff_range (localized_compact_cutoff_laws hG) x)).1.
have[b hGauge]:=@hFinite g (conj (compact_cutoff_function (localized_compact_cutoff_laws hG)) hNonnegative)
  (localized_compact_cutoff_support hG).
have hValueOff e:0<e ->e<r ->forall x,~smooth_compact_carrier C x ->values (P e) x=0.
  move=>he her.
  exact:((@smooth_function_compact_support_iff R X Y N NY hN hNY U E ev hE C
    (smooth_test_inclusion hE (P e))).1 (hP e he her).2).
have hUniform eta:0<eta ->exists d:R,0<d /\
    forall e:R,0<e ->e<d ->forall x,NY (values (P e) x-w x)<eta.
  move=>hEta; have[d [hd [_ hBound]]]:=hApprox eta hEta.
  by exists d.
have[t hLimit]:=@distribution_variation_approximation_limit R X Y NY hNY DT values S P w
  (smooth_compact_carrier C) g b r hr hNonnegative
  (fun x hx=>compact_cutoff_on_set (localized_compact_cutoff_laws hG) hx)
  hGauge hValueOff hUniform.
exists t,r; split=>//; exists C,P; split; first exact hP.
by split.
Qed.
End DistributionCompactContinuousLimit.
