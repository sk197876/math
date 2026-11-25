(** Federer (1969), 4.1.21, p. 378: the current
    restricted to a compact subset has support in that
    same subset. Reuse the actual subset-integral action of
    4.1.7, p. 356, and the old test-annihilation support
    criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMeasurableRestriction CurrentSupportGeometry SmoothCompactSet
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation IsotropyGroupTopology
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureSubsetIntegral
  MeasureIntegralUniqueness SubsetIntegralAlmostZero SummableRealFunctionUP
  PartialFunctionUP PairingLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentCompactMeasurableRestrictionSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT:=(current_domain R n U).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m U hU T hT).
Local Notation eta:=(@NormalisedCurrent.auxiliary_density R h2 n m U hU T hT).
Local Notation hBase:=(normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n m U hU T hT)).
Local Notation hm:=(distribution_representation_measure hBase).
Variable A:set UT.
Hypothesis hA:compact A.
Hypothesis hMeasurable:measure_measurable mu A.
Local Notation S:=(@current_measurable_restriction R h2 n m U hU T hT A hMeasurable).

(** Source for [current_compact_measurable_restriction_support]:
    the support containment used before applying 4.1.20 in
    the second corollary of 4.1.21, p. 378. The
    compact set lives in the original relative domain U.
    The conclusion uses its literal ambient image, including
    the empty set, with no replacement current or coefficient. *)
Theorem current_compact_measurable_restriction_support:
  @current_support R h2 n U hU m S `<=` (set_val @` A).
Proof.
have hImage:@compact XT (set_val @` A).
  apply:continuous_compact hA.
  exact:continuous_subspaceT (@set_type_val_continuous XT U).
have hImageU:(set_val @` A) `<=` U.
  move=>x [z hz <-];exact:set_valP.
pose K:=@Build_smooth_compact_set R X NX hNX U (set_val @` A) hImageU hImage.
apply:(@current_support_compact_criterion R h2 n m U hU K S).2=>psi hPsi.
have hZero x:A x->@current_test_value R h2 n U hU m psi (set_val x)=0.
  move=>hx;apply:contrapT=>hNonzero.
  have hSupport:=@smooth_function_nonzero_in_support R X (A_m X R^o m)
    NX hNX U (@current_test_space R h2 n U hU m)
    (@current_test_value R h2 n U hU m) psi (set_val x) (set_valP x) hNonzero.
  apply:(hPsi (set_val x) hSupport).2;by exists x.
have hZeroIntegral:is_measure_subset_integral mu A (real_total_integrand
    (fun x:UT=>pairing (eta x) (@current_test_value R h2 n U hU m psi (set_val x)))) 0%E.
  apply:(@subset_integral_almost_zero R UT mu hm A).
  apply:(@measure_almost_everywhere_on_implication R UT mu A _).2.
  apply:(@measure_almost_everywhere_mono R UT mu hm setT).
  - move=>x _ hx.
    change (partial_function_graph (real_total_integrand
      (fun y:UT=>pairing (eta y)
        (@current_test_value R h2 n U hU m psi (set_val y)))) x 0%E).
    apply:(@real_total_integrand_graph R UT _ x 0%E).2.
    by rewrite (hZero x hx) -pairing_rightE linear0.
  - exact:(@measure_almost_everywhere_true R UT mu hm).
have hIntegral:=@current_measurable_restriction_action R h2 n m U hU T hT A hMeasurable psi.
exact:(EFin_inj (measure_integral_unique hIntegral hZeroIntegral)).
Qed.
End CurrentCompactMeasurableRestrictionSupport.
