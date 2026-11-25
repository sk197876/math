(** Federer (1969), 4.1.5, p. 350: the
    original compact smooth convolutions approximate a
    compact continuous field in the Radon L1 norm.
    Uniform convergence has one compact support bound;
    Radon compact finiteness turns that bound into
    arbitrarily small integral norm error. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FunctionLatticeUP CompactSupportFunctionUP IsotropyGroupTopology
  CompactContinuousVectorFields CompactContinuousVectorZeroExtension CompactContinuousOpenExtensionLinear
  CompactContinuousVectorAlgebra CompactUniformApproximationUP CompactContinuousTestApproximation
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionSubspaceTestValues
  MeasureUP MeasureBasic RadonMeasureUP RealIntegralFunctionalUP SummableRealFunctionUP MeasureIntegralUP
  CompactFieldUniformIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousTestLoneApproximation.
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
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable F:(UT->R)->R.
Hypothesis hF:is_real_integral_functional mu
  (positive_function_lattice (@compactly_supported_continuous_functions R UT)) F.

(** Source for [compact_continuous_field_test_lone_approximation]:
    the actual D(U,Y) approximates every original
    compact continuous field in Radon L1 error,
    Federer 4.1.5, p. 350. The proof needs
    neither finite total measure nor positive compact
    mass nor separability of the whole Banach target. *)
Theorem compact_continuous_field_test_lone_approximation (w:UT->Y):
  @compact_continuous_vector_fields R UT Y NY hNY w ->
  forall epsilon:R,0<epsilon ->exists psi:DT,exists a:R,
    is_measure_integral mu (real_total_integrand (fun x:UT=>NY (w x-dvalues psi x))) a%:E /\
    a<epsilon.
Proof.
move=>hw epsilon hEpsilon.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
pose wG:=@compact_vector_open_extension R XT U Y w.
have hGlobal:=@compact_vector_open_extension_domain R XT U Y NY hNY
  (@metric_hausdorff R XT) hOpen w hw.
have[P [C [hC [hCU [r [hR [hOff hUniform]]]]]]]:=
  @compact_continuous_field_test_approximation R n Y NY hNY hY U hU E ev hE wG hGlobal.1 hGlobal.2.
pose K:set UT:=(set_val @^-1` C) `|` @real_function_support R UT (fun x=>NY (w x)).
have hK:compact K:=compactU (@set_type_compact_preimage XT U C hC hCU) hw.2.
have hFinite:mu K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K)); exact:(@radon_compact_finite R UT mu hr K hK).
pose m:=fine (mu K).
have hM:0<=m.
  have h:=measure_nonnegative hm K; by rewrite -(fineK hFinite) lee_fin in h.
have hDen:0<m+1 by lra.
pose delta:=epsilon/(m+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have[d [hd hApprox]]:=hUniform delta hDelta.
pose e:=Num.min r d/2.
have hMin:0<Num.min r d by rewrite lt_min hR hd.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have hSmall:e<Num.min r d by rewrite /e; lra.
have /andP [her hed]:(e<r)&&(e<d) by rewrite -lt_min.
pose u:=fun x:UT=>w x-dvalues (P e) x.
have hTest:=@smooth_test_original_continuous_field R X Y N NY hN hNY U E ev hE (P e).
have hu:=@compact_continuous_vector_subtract R UT Y NY hNY w (dvalues (P e)) hw hTest.
have hBound:forall x:UT,NY (u x)<=delta.
  move=>x; have h:=hApprox e he hed (set_val x).
  rewrite /wG (@compact_vector_open_extension_value R XT U Y w x) in h.
  rewrite /u (real_seminorm_subtract hNY.1); exact:ltW h.
have hUOff:forall x:UT,~K x ->u x=0.
  move=>x hx.
  have hNoC:~C (set_val x) by move=>h; apply:hx; by left.
  have hNoW:~@real_function_support R UT (fun x=>NY (w x)) x.
    move=>h; apply:hx; by right.
  rewrite /u (@compact_continuous_vector_zero_off_norm_support R UT Y NY hNY w x hNoW).
  have hPhi:=hOff e he her (set_val x) hNoC.
  change (dvalues (P e) x=0) in hPhi.
  by rewrite hPhi subrr.
have[a [hI hA]]:=@compact_field_uniform_integral_bound R UT Y NY hNY mu hm hr F hF u K delta
  hu hK hDelta hBound hUOff.
exists (P e),a; split; first exact hI.
have hStrict:delta * m<delta*(m+1) by rewrite ltr_pM2l //; lra.
have hBudget:delta*(m+1)=epsilon by rewrite /delta divfK ?gt_eqF.
rewrite hBudget in hStrict; exact:le_lt_trans hA hStrict.
Qed.
End CompactContinuousTestLoneApproximation.
