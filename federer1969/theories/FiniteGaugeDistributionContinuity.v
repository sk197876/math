(** Federer (1969), 4.1.5, pp. 349–350:
    a linear test functional with finite
    original gauge is an actual distribution.
    The original final topology is tested
    on each compact-support step, using
    only the order-zero derivative seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP RealSeminormOperations NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormOpenTopology OpenFamilyTopologyUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FiniteNormEquivalence ContinuousMultilinearSealed LinearSubspaceRepresentationUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionSeminormFamily SmoothDerivativeSeminormUP SmoothDerivativeSeminormLaws SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology DistributionLocalBound SeminormBallDomination
  SeminormRealDualBound FunctionLatticeUP CompactCutoffUP LocalizedCompactCutoffUP
  DistributionVariationUP DistributionVariationBasic DistributionVariationFinite DistributionFiniteVariationUP
  DistributionVariationDomainFinite DistributionFiniteGaugeCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteGaugeDistributionContinuity.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hN).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Variable D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y N NY hN hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation DK := (smooth_fixed_test_space hE).
Local Notation k := (smooth_fixed_test_inclusion hE).
Local Notation j := (smooth_test_step hE).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Variable S:Hom DT R^o.

(** Source for [finite_gauge_distribution_continuous]: finite
    original variation gives the actual distribution
    continuity required in the final compactness
    assertion of Federer 4.1.5, p. 350.
    The proof uses no homogeneous property of M
    and does not alter the literal final topology. *)
Theorem finite_gauge_distribution_continuous:
  @is_finite_distribution_variation R XT U Y NY DT values S ->
  open_family_continuous (smooth_test_opens hE hD)
    (norm_open_family (@scalar_absolute_value_norm R)) S.
Proof.
move=>hFinite.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hOutside:forall phi:DT,forall x:XT,~U x ->values phi x=0.
  move=>phi x hx; exact:(@smooth_test_value_outside R X Y N NY hN hNY U E ev hE phi x hx).
have hAmbient:=@distribution_domain_finite_majorants R XT U Y NY hNY DT values hOutside S hFinite.
apply:(@distribution_continuity_local_bound R X Y N NY hN hNY U hU E ev hE D hD S).2=>K.
have[g [b [hG hGauge]]]:=@distribution_finite_gauge_cutoff R XT U Y NY DT values S
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN)
  hOpen hAmbient (smooth_compact_carrier K) (smooth_compact_is_compact K) (smooth_compact_in_domain K).
have hNonnegative:forall x:XT,0<=g x.
  move=>x; exact:(andP (compact_cutoff_range (localized_compact_cutoff_laws hG) x)).1.
have hBNonnegative:0<=b.
  have h:=@distribution_variation_nonnegative R XT Y NY hNY DT values S g b%:E hNonnegative hGauge.
  by move:h; rewrite lee_fin.
pose LK:Hom (DK K) R^o:=hom_comp S (j K).
pose p:=fun f:DK K=>nu K 0%N (k K f).
have hP:is_real_seminorm p.
  exact:(@real_seminorm_linear_precompose R (DK K) E (nu K 0%N)
    (smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hD K 0%N))
    (k K) (hom_linear (k K))).
have hQ:is_real_seminorm (fun f:DK K=>`|LK f|).
  exact:(@real_seminorm_linear_precompose R (DK K) R^o (fun t:R^o=>`|t|)
    (@scalar_absolute_value_norm R).1 LK (hom_linear LK)).
pose delta:=(b+1)^-1.
have hBOne:0<b+1 by lra.
have hDelta:0<delta by rewrite /delta invr_gt0.
have hSmall f:p f<delta ->`|LK f|<1.
  move=>hPF.
  have hSupport:=subspace_representation_member (smooth_fixed_test_space_laws hE K) f.
  have hZero:=(@smooth_function_compact_support_iff R X Y N NY hN hNY U E ev hE K (k K f)).1 hSupport.
  have hNorm:forall x:XT,NY (values (j K f) x)<=delta*g x.
    move=>x; change (is_true (NY (ev (inc (j K f)) x)<=delta*g x)).
    rewrite smooth_test_step_evaluation.
    case:(pselect (smooth_compact_carrier K x))=>hx.
    - rewrite (compact_cutoff_on_set (localized_compact_cutoff_laws hG) hx) mulr1.
      have hValue:=smooth_derivative_seminorm_bound (smooth_function_derivative_seminorm_laws hD K 0%N)
        (k K f) (leqnn 0%N) hx.
      rewrite (@smooth_derivative_zero_norm R X Y N NY hN hNY U E ev D hD
        (k K f) x (smooth_compact_in_domain K x hx)) in hValue.
      exact:le_trans hValue (ltW hPF).
    - rewrite (hZero x hx) (real_seminorm_zero hNY.1).
      exact:mulr_ge0 (ltW hDelta) (hNonnegative x).
  have hBound:=@distribution_variation_finite_scaled_bound R XT Y NY hNY DT values S g b delta
    hGauge hDelta (j K f) hNorm.
  have hProduct:delta*b<1.
    have hEq:delta*(b+1)= 1 by rewrite /delta mulVf // gt_eqF.
    nra.
  exact:le_lt_trans hBound hProduct.
have hBound:=@seminorm_unit_ball_domination R (DK K) p (fun f:DK K=>`|LK f|) hP hQ delta hDelta hSmall.
have hConstant:0<=2/delta by rewrite divr_ge0 // ltW.
have[M hInteger]:=@seminorm_bound_integer_constant R (DK K) p hP LK (2/delta) hConstant hBound.
exists 0%N,M; exact hInteger.
Qed.
End FiniteGaugeDistributionContinuity.
