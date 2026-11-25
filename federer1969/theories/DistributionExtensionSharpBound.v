(** Federer (1969), 4.1.5, pp. 349–350:
    the original continuous extension satisfies the
    sharp bound T(w)<=||S||(||w||). The printed
    norm-tail estimate and arbitrarily small positive
    eta give the assertion, with no changed gauge. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology CompleteMetricUP
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  FunctionLatticeUP CompactSupportFunctionUP CompactCutoffUP LocalizedCompactCutoffUP CompactCutoffPlateau
  CompactContinuousDomainFields SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  SmoothingKernelSealed SmoothingDilationSealed DistributionVariationUP DistributionVariationBasic
  DistributionVariationDomainFinite DistributionFiniteVariationUP DistributionContinuousExtensionUP DistributionNormTailEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionExtensionSharpBound.
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
Local Notation values := (smooth_test_values_hom hE).
Variable S:Hom DT R^o.
Hypothesis hFinite:@is_finite_distribution_variation R XT U Y NY DT values S.
Variable T:(X->Y)->R.
Hypothesis hT:@is_distribution_continuous_extension R XT U Y NY hNY DT values S T.

(** Source for [distribution_extension_sharp_variation_bound]:
    the sharp original upper bound for T(w) in
    Federer 4.1.5, pp. 349–350. Both printed
    convolution estimates have already been proved for
    the actual fields and compact test spaces. *)
Theorem distribution_extension_sharp_variation_bound w b:
  @compact_continuous_domain_fields R XT U Y NY hNY w ->
  is_distribution_variation_value NY values S (fun x=>NY (w x)) b%:E ->
  T w<=b.
Proof.
move=>hw hGaugeW.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hOutside:forall psi:DT,forall x:XT,~U x ->values psi x=0.
  move=>psi x hx; exact:(@smooth_test_value_outside R X Y N NY hN hNY U E ev hE psi x hx).
have hAmbient:=@distribution_domain_finite_majorants R XT U Y NY hNY DT values hOutside S hFinite.
have[g [W [hG [hW [hKW hOne]]]]]:=@localized_compact_cutoff_plateau R XT
  (@real_function_support R XT (fun x=>NY (w x))) U
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN)
  hw.1.2 hOpen hw.2.
have hNonnegative:function_nonnegative g.
  move=>x; exact:(andP (compact_cutoff_range (localized_compact_cutoff_laws hG) x)).1.
have hPositive:@positive_function_lattice R X (@compactly_supported_continuous_functions R XT) g.
  exact:conj (compact_cutoff_function (localized_compact_cutoff_laws hG)) hNonnegative.
have[c hGaugeG]:=@hAmbient g hPositive (localized_compact_cutoff_support hG).
have hCNonnegative:=@distribution_variation_nonnegative R X Y NY hNY DT values S g c%:E hNonnegative hGaugeG.
have hc:0<=c by move:hCNonnegative; rewrite lee_fin.
have hC:0<c+1 by lra.
pose phi:=@SmoothingKernel.value R n.
pose family:=@SmoothingDilation.value R n phi.
apply/ler_addgt0Pr=>epsilon hEpsilon.
pose eta:=epsilon/(c+1).
have hEta:0<eta by rewrite /eta divr_gt0.
have hEstimate:=@distribution_norm_tail_estimate R n Y NY hNY hY U hU E ev hE S T hT
  phi (@SmoothingKernel.laws R n) family (@SmoothingDilation.laws R n phi)
  w b g c W hw hW hKW hNonnegative hOne hGaugeW hGaugeG eta hEta.
have hCoefficient:c<=c+1 by lra.
have hError:eta*c<=epsilon.
  have h:=ler_wpM2l (ltW hEta) hCoefficient.
  by rewrite /eta divfK ?gt_eqF // in h.
exact:le_trans hEstimate (lerD (lexx b) hError).
Qed.
End DistributionExtensionSharpBound.
