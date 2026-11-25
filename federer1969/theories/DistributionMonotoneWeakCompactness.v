(** Federer (1969), 4.1.5, p. 350:
    the original M-bounded distributions form
    a compact set in the actual weak dual.
    The bounds imply finite original gauge,
    hence continuity for the literal final
    topology. M need not be homogeneous. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP
  OpenFamilyTopologyMathcomp GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearSealed SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothTestTopology ContinuousRealDual FunctionLatticeUP CompactSupportFunctionUP
  DistributionVariationDomain DistributionSubspaceTestValues CompactContinuousVectorFields
  DistributionMonotoneGaugeBounds FiniteGaugeDistributionContinuity BoundedContinuousDualCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionMonotoneWeakCompactness.
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
Local Notation values := (smooth_test_values_hom hE).
Local Notation UT := (set_type (U:set XT)).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation W := (open_family_topological_space (@continuous_real_dual_weak_laws R DT SO hSO).1).
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R UT)).
Variable M:(UT->R)->R.
Hypothesis hMonotone:forall f g,Kplus f ->Kplus g ->function_le f g ->M f<=M g.
Let hNormTest phi:=@compact_continuous_vector_field_norm R UT Y NY hNY (dvalues phi)
  (@smooth_test_original_continuous_field R X Y N NY hN hNY U E ev hE phi).
Local Notation GBound := (@is_original_distribution_gauge_bounded R UT Y NY hNY DT dvalues M).

(** Source for [distribution_original_bounded_set_equality]: the
    exact equality of the two bounded sets
    displayed in Federer 4.1.5, p. 350,
    in the actual original distribution space. *)
Theorem distribution_original_bounded_set_equality:
  [set T:W|GBound (eD T)]=
    [set T:W|forall phi:DT,eD T phi<=M (fun x=>NY (dvalues phi x))].
Proof.
apply/seteqP; split=>T hT.
- exact:(@original_distribution_gauge_test_bounds_iff R UT Y NY hNY DT dvalues hNormTest M hMonotone (eD T)).1 hT.
- exact:(@original_distribution_gauge_test_bounds_iff R UT Y NY hNY DT dvalues hNormTest M hMonotone (eD T)).2 hT.
Qed.

(** Source for [distribution_original_monotone_bound_weak_compact]:
    the complete final compactness assertion of
    Federer 4.1.5, p. 350. The original
    monotone finite M is retained, without
    homogeneity or joint continuity of the
    literal final test topology. *)
Theorem distribution_original_monotone_bound_weak_compact:
  compact [set T:W|GBound (eD T)].
Proof.
have hAdmissible (L:Hom DT R^o):
    (forall phi:DT,L phi<=M (fun x=>NY (dvalues phi x))) ->
    open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) L.
  move=>hBound.
  have hFinite:=@original_distribution_test_bounds_finite R UT Y NY hNY DT dvalues hNormTest M hMonotone L hBound.
  exact:(@finite_gauge_distribution_continuous R n Y NY hNY U hU E ev hE D hD L hFinite).
have hCompact:=@bounded_continuous_real_dual_weak_compact R DT SO hSO
  (fun phi:DT=>M (fun x=>NY (dvalues phi x))) hAdmissible.
rewrite distribution_original_bounded_set_equality; exact hCompact.
Qed.
End DistributionMonotoneWeakCompactness.
