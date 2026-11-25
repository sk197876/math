(** Federer (1969), 4.1.7, p. 358:
    if the original variation is k times the
    mass-density measure, transfer its normalized
    multivector density to that measure. Borel
    representatives and the original change-of-density
    laws retain every actual test and zero weight. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionPreimages Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms MetricSubsetBackground
  CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces CurrentSpaces CurrentMultivectorDual MultivectorDualSealed
  CurrentUnitBorelDensity CurrentDensityNormMeasurable CurrentUnitDensityTestIntegral
  CurrentCoefficientCompleteness AbstractUnitDualPairingMeasurable AbstractDualPartialPairing MeasurableGraphEquivalence
  OpenFamilyTopologyMathcomp PartialFunctionBasic SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostEquality MeasurableFunctionUP RealTotalMeasurabilityProjection MeasurableScalarVectorProduct
  FiniteNormMetricPolish BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity
  BoundedRealDensityMeasure RealFiniteDensityIntegral MeasureDensityUP MeasureIntegralUP MeasureIntegralAlmostEquality
  SmoothFunctionSpaceUP SmoothTestEvaluation DistributionVariationDomain DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBoundedDensityTransfer.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Y := (A_m X R^o m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation UM := (metric_subset (U:set XT)).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT (smooth_test_values_hom hE)).
Variables mu nu:set UT->\bar R.
Hypotheses (hm:is_measure mu) (hn:is_measure nu).
Hypotheses (hr:is_radon_measure mu) (hs:is_radon_measure nu).
Variable k:UT->R.
Hypothesis hk:is_measure_measurable_function mu (real_total_integrand k).
Hypothesis hRange:forall x,0<=k x<=1.
Hypothesis hDensity:is_measure_density mu (real_total_integrand k) nu.
Variable eta:UT->V.
Hypothesis hEta:is_measure_measurable_function nu
  (partial_function_total (fun x=>(eta x:open_family_topological_space hO.1))).
Hypothesis hEtaBound:forall x,VN (eta x)<=1.
Hypothesis hEtaUnit:measure_almost_everywhere nu [set x|VN (eta x) = 1].
Variable S:Hom DT R^o.
Hypothesis hAction:is_distribution_integral_action nu ed eta dvalues S.

(** Source for [current_bounded_density_transfer_full]: the
    original current has a unit-bounded weakly
    measurable density z with mass(z)=k almost
    everywhere for the dominating Radon measure,
    supporting Federer 4.1.7, p. 358, by
    2.4.10 and the original normalized representation.
    The same transfer applies to every total
    field measurable for the dominating measure,
    as needed in the Baire projection
    of 4.1.7, p. 359. *)
Theorem current_bounded_density_transfer_full:
  exists z:UT->V,
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(z x:open_family_topological_space hO.1))) /\
    (forall x,VN (z x)<=1) /\
    measure_almost_everywhere mu [set x|VN (z x)=k x] /\
    is_distribution_integral_action mu ed z dvalues S /\
    forall f:UT->real_norm_metric_space (@current_form_comass_real_norm R h2 n m),
      is_measure_measurable_function mu (partial_function_total f)->forall a,
      is_measure_integral nu (real_total_integrand (fun x=>ed (eta x) (f x))) a<->
      is_measure_integral mu (real_total_integrand (fun x=>ed (z x) (f x))) a.
Proof.
have [w [hWBorel [hWBound hAgree]]]:=
  @current_unit_density_borel_version R h2 n m U hU nu hn hs eta hEta hEtaBound.
have hWNorm:is_measure_measurable_function mu
    (partial_function_total (fun x=>(w x:real_norm_metric_space hVN))).
  constructor.
  - rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
  - move=>G hG; rewrite partial_function_total_preimage.
    exact:(borel_regular_borel_measurable hm (radon_borel_regular hm hr) (hWBorel G hG)).
have hW:=@current_density_weak_topology_measurable R h2 n m UT mu hm w hWNorm.
have hKReal:=@real_total_measurability_projection R UT mu hm k hk.
have [d [e he]]:=@current_vector_finite_basis R h2 n m.
have hSep:=@finite_norm_metric_separable R V VN hVN d e he.
pose z x:=k x*:w x.
have hZNorm:=@measurable_scalar_vector_product R UT V VN hVN mu hm k w hSep hKReal hWNorm.
have hZ:=@current_density_weak_topology_measurable R h2 n m UT mu hm z hZNorm.
have hZBound x:VN (z x)<=1.
  have hk0:0<=k x:=(andP (hRange x)).1.
  rewrite /z (real_seminorm_scale hVN.1) (ger0_norm hk0).
  have h:=ler_wpM2l hk0 (hWBound x).
  rewrite mulr1 in h; exact:le_trans h (andP (hRange x)).2.
have hWUnit:measure_almost_everywhere nu [set x|VN (w x) = 1].
  apply:(@measure_almost_everywhere_mono R UT nu hn _ _ _
    (measure_almost_everywhere_and hn hAgree hEtaUnit))=>x [hEq hOne].
  exact:(eq_trans (congr1 VN (esym hEq)) hOne).
have hPositive:=@unit_real_density_measure_nonnegative R UM mu hm k hRange.
have hWeighted:=@finite_real_density_weight_agreement R UT mu nu hm k
  (fun x=>VN (w x)) (fun _=>1) hDensity hk hPositive hWUnit.
have hZMass:measure_almost_everywhere mu [set x|VN (z x)=k x].
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hWeighted)=>x hx.
  change (VN (w x)*k x = 1*k x) in hx.
  rewrite mul1r in hx.
  have hScale:VN (z x)=k x*VN (w x).
    have h:=@real_seminorm_scale R V VN hVN.1 (k x) (w x).
    rewrite (ger0_norm (andP (hRange x)).1) in h;exact:h.
  exact:(eq_trans hScale (eq_trans (mulrC (k x) (VN (w x))) hx)).
exists z; split; first exact:hZ.
split; first exact:hZBound.
split; first exact:hZMass.
split.
- move=>psi.
  have hOriginal:=hAction psi.
  have hWIntegral:is_measure_integral nu
      (real_total_integrand (fun x=>ed (w x) (dvalues psi x))) (S psi)%:E.
    apply:(measure_integral_almost_equal hn hOriginal).
    apply:(@measure_almost_everywhere_mono R UT nu hn _ _ _ hAgree)=>x hx.
    exists (ed (eta x) (dvalues psi x))%:E; split;
      first by rewrite real_total_integrand_graph.
    by rewrite real_total_integrand_graph -hx.
  have [c hPair]:=@current_unit_density_test_integral_finite R h2 n m U hU mu hm hr
    w hW hWBound psi.
  have hProduct:=(@real_finite_density_integral_iff R UT mu nu hm k
    (fun x=>ed (w x) (dvalues psi x)) hDensity hk hPositive hPair.1 (S psi)%:E).1 hWIntegral.
  have hPoint:(fun x=>ed (w x) (dvalues psi x)*k x)=(fun x=>ed (z x) (dvalues psi x)).
    apply:funext=>x; rewrite /z linearZ hom_scaleE; exact:mulrC.
  by rewrite hPoint in hProduct.
- move=>f hF a.
  have hRaw:=@abstract_unit_dual_pairing_measurable R UT Y
    (@current_form_comass R h2 n m) (@current_form_comass_real_norm R h2 n m)
    (@current_form_separable R h2 n m) V ed VN
    (@current_multivector_continuous_dual R h2 n m)
    (@current_multivector_weak_opens R n m) hO mu hm w (partial_function_total f) hW hWBound hF.
  have hPair:=measurable_function_graph_equivalent
    (@abstract_dual_partial_pairing_total_graph R UT Y V ed w f) hRaw.
  have hIff:=@real_finite_density_integral_iff R UT mu nu hm k
    (fun x=>ed (w x) (f x)) hDensity hk hPositive hPair a.
  have hPoint:(fun x=>ed (w x) (f x)*k x)=(fun x=>ed (z x) (f x)).
    apply:funext=>x;rewrite /z linearZ hom_scaleE;exact:mulrC.
  rewrite hPoint in hIff.
  have hEquality:measure_almost_equal nu
      (real_total_integrand (fun x=>ed (eta x) (f x)))
      (real_total_integrand (fun x=>ed (w x) (f x))).
    apply:(@measure_almost_everywhere_mono R UT nu hn _ _ _ hAgree)=>x hx.
    exists (ed (eta x) (f x))%:E;split;rewrite real_total_integrand_graph;first by [].
    by rewrite -hx.
  split=>hIntegral.
  + apply:hIff.1;exact:(measure_integral_almost_equal hn hIntegral hEquality).
  + exact:(measure_integral_almost_equal hn (hIff.2 hIntegral)
      (measure_almost_equal_sym hEquality)).

Qed.

(** Source for [current_bounded_density_transfer]: the
    original bounded-density transfer used by
    the exact variation proof, supporting
    Federer 4.1.7, p. 358. The
    stronger measurable-field formula has just
    been proved from the same original densities. *)
Theorem current_bounded_density_transfer:
  exists z:UT->V,
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(z x:open_family_topological_space hO.1))) /\
    (forall x,VN (z x)<=1) /\
    measure_almost_everywhere mu [set x|VN (z x)=k x] /\
    is_distribution_integral_action mu ed z dvalues S.
Proof.
have [z [hZ [hBound [hMass [hActionZ hFields]]]]]:=current_bounded_density_transfer_full.
exists z;split;first exact:hZ.
split;first exact:hBound.
split;[exact:hMass|exact:hActionZ].
Qed.
End CurrentBoundedDensityTransfer.
