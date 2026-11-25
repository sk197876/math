(** Federer (1969), 4.1.5, p. 350: the
    extension on the original compact continuous D
    is linear and order bounded. Scalar zero extension
    preserves the original gauge, so the sharp ambient
    estimate supplies every bound required by 2.5.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology CompleteMetricUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  FunctionLatticeUP CompactSupportFunctionUP VectorDaniellHypotheses OrderBoundedVectorFunctionalUP
  OpenSubspaceExtension CompactContinuousDomainFields CompactContinuousVectorFields CompactContinuousVectorZeroExtension CompactContinuousOpenExtensionLinear
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationUP DistributionVariationBasic
  DistributionVariationDomain DistributionFiniteVariationUP DistributionContinuousExtensionUP DistributionExtensionSharpBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_subspace_extension]: the
    original T on compact continuous fields defined
    on U, obtained from its normalized ambient
    representative, Federer 4.1.5, pp. 349–350. *)
Definition distribution_subspace_extension (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (T:(X->Y)->R) (w:set_type U->Y):R:=
  T (@compact_vector_open_extension R X U Y w).

Section DistributionSubspaceExtension.
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
Variable S:Hom DT R^o.
Hypothesis hFinite:@is_finite_distribution_variation R XT U Y NY DT values S.
Variable T:(X->Y)->R.
Hypothesis hT:@is_distribution_continuous_extension R XT U Y NY hNY DT values S T.
Local Notation Q := (@compact_continuous_vector_fields R UT Y NY hNY).
Local Notation TU := (@distribution_subspace_extension R XT U Y T).

(** Source for [distribution_subspace_extension_original_bound]:
    the exact original gauge bounds T on every original
    norm-bounded compact continuous field, Federer 4.1.5,
    p. 350. This retains the prescribed gauge value. *)
Theorem distribution_subspace_extension_original_bound f b:
  @positive_function_lattice R UT (@compactly_supported_continuous_functions R UT) f ->
  is_distribution_variation_value NY dvalues S f b%:E ->
  forall w, Q w ->function_le (fun x=>NY (w x)) f ->TU w<=b.
Proof.
move=>hf hGaugeF w hw hBound.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hGlobal w0:Q w0 ->
    @compact_continuous_domain_fields R XT U Y NY hNY (compact_vector_open_extension w0).
  exact:(@compact_vector_open_extension_domain R XT U Y NY hNY (@metric_hausdorff R XT) hOpen w0).
have hOutside:forall psi:DT,forall x:XT,~U x ->values psi x=0.
  move=>psi x hx; exact:(@smooth_test_value_outside R X Y N NY hN hNY U E ev hE psi x hx).
have hNormPositive:@positive_function_lattice R UT (@compactly_supported_continuous_functions R UT)
    (fun x=>NY (w x)).
  split; first exact:(@compact_continuous_vector_field_norm R UT Y NY hNY w hw).
  move=>x; exact:(real_seminorm_nonnegative hNY.1 (w x)).
have[a hGaugeNorm]:=@hFinite (fun x=>NY (w x)) hNormPositive.
have hComparison:=@distribution_variation_monotone R UT Y NY DT dvalues S
  (fun x=>NY (w x)) f a%:E b%:E hGaugeNorm hGaugeF hBound.
rewrite lee_fin in hComparison.
have hFullGauge:=(@distribution_domain_gauge_value R XT U Y NY hNY DT values hOutside S
  (fun x=>NY (w x)) a%:E).1 hGaugeNorm.
rewrite -(@compact_vector_open_extension_norm R XT U Y NY hNY w) in hFullGauge.
have hSharp:=@distribution_extension_sharp_variation_bound R n Y NY hNY hY U hU E ev hE S hFinite T hT
  (compact_vector_open_extension w) a (hGlobal w hw) hFullGauge.
exact:le_trans hSharp hComparison.
Qed.

(** Source for [distribution_subspace_extension_order_bounded]:
    linearity and all finite variation bounds for the
    original T in Federer 4.1.5, p. 350. Thus
    the hypotheses of 2.5.14 are conclusions from
    the original gauge condition, not added premises. *)
Theorem distribution_subspace_extension_order_bounded:
  is_order_bounded_vector_functional NY (@compactly_supported_continuous_functions R UT) Q TU.
Proof.
have hOpen:@open XT U.
  rewrite openE=>x hx; exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hGlobal w0:Q w0 ->
    @compact_continuous_domain_fields R XT U Y NY hNY (compact_vector_open_extension w0).
  exact:(@compact_vector_open_extension_domain R XT U Y NY hNY (@metric_hausdorff R XT) hOpen w0).
have hOutside:forall psi:DT,forall x:XT,~U x ->values psi x=0.
  move=>psi x hx; exact:(@smooth_test_value_outside R X Y N NY hN hNY U E ev hE psi x hx).
constructor.
- move=>w v hw hv; rewrite /distribution_subspace_extension compact_vector_open_extension_add.
  exact:(@distribution_extension_add R XT U Y NY hNY DT values S T hT
    (compact_vector_open_extension w) (compact_vector_open_extension v) (hGlobal w hw) (hGlobal v hv)).
- move=>c w hw; rewrite /distribution_subspace_extension compact_vector_open_extension_scale.
  exact:(@distribution_extension_scale R XT U Y NY hNY DT values S T hT c
    (compact_vector_open_extension w) (hGlobal w hw)).
- move=>f hf.
  have[b hGaugeF]:=@hFinite f hf.
  exists b=>w hw hBound.
  exact:(distribution_subspace_extension_original_bound hf hGaugeF hw hBound).
Qed.
End DistributionSubspaceExtension.
