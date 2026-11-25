(** Federer (1969), 4.1.26, pp. 383–384:
    current constancy gives almost constancy of
    its original locally summable density. The
    difference from a constant remains locally
    integrable. Exact variation of the zero
    current then makes that difference zero
    almost everywhere, without a bounded-density premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormMetricContinuity
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms CurrentMultivectorDual
  MultivectorDualSealed CurrentSpaces CurrentDomain CurrentEvaluation CurrentIntegrationCriterion
  OpenCurrentDensityUP OpenCurrentDensitySealed CurrentContinuousOpenDensity CurrentDensityNormMeasurable
  CurrentOpenDensityZero DistributionIntegrationRepresentationUP OpenFamilyTopologyMathcomp
  MeasureUP RadonMeasureUP RadonBorelRegularity MeasureIntegralUP MeasureIntegralUniqueness
  MeasureSubsetIntegral MeasureAlmostUP MeasureAlmostBasic PartialFunctionBasic
  MeasurableFunctionUP MeasurableTotalBasic MeasurableTotalCutoff BorelFunctionBasic
  MeasureStepIntegralIdentification RealSubsetIntegralGraph SummableRealFunctionUP SummableRealArithmetic
  VectorDaniellPairingMeasurability NormMetricScaleContinuity
  RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentOpenDensityConstantAgreement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation VT:=(real_norm_metric_space hVN).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT:=(current_domain R n U).
Variable gamma:set UT->\bar R.
Hypothesis hGamma:is_measure gamma.
Hypothesis hRadon:is_radon_measure gamma.
Variable xi:UT->V.
Hypothesis hField:@is_locally_integrable_open_current_density R h2 n m U gamma xi.
Variable z:V.

(** Source for [current_open_density_subtract_constant_integrable]:
    the original local summability is closed
    under subtracting a constant field, supporting
    the constancy inference of 4.1.26, p. 384.
    Every compact set retains a finite
    integral; total mass need not be finite. *)
Theorem current_open_density_subtract_constant_integrable:
  @is_locally_integrable_open_current_density R h2 n m U gamma
    (fun x=>xi x-z).
Proof.
have hXi:=@current_density_mass_topology_measurable R h2 n m UT gamma hGamma xi hField.1.
have hTranslate:continuous (fun v:VT=>(v-z:VT)).
  apply:(@metric_fixed_lipschitz_continuous R VT VT _ 1 ler01)=>a b.
  change (is_true (VN ((a-z)-(b-z))<=1*VN (a-b))).
  by rewrite opprB addrA subrK mul1r.
have hDiff:=@measurable_total_borel_postcomposition R UT VT VT gamma hGamma
  xi (fun v=>v-z) hXi (continuous_borel_function hTranslate).
have hNorm:=@measurable_total_borel_postcomposition R UT VT
  (real_line_metric R) gamma hGamma (fun x=>xi x-z) VN hDiff
  (continuous_borel_function (@real_norm_metric_norm_continuous R V VN hVN)).
have hZ:@is_locally_integrable_open_current_density R h2 n m U gamma (fun _=>z).
  apply:(@current_continuous_open_density_integrable R h2 n m U gamma hGamma hRadon).
  exact:cst_continuous.
split.
- exact:(@current_density_weak_topology_measurable R h2 n m UT gamma hGamma _ hDiff).
- move=>K hK.
  have hKMeas:measure_measurable gamma K:=radon_compact_measurable hGamma hRadon hK.
  have[a hA]:=hField.2 K hK.
  have[b hB]:=hZ.2 K hK.
  pose f:=fun x:UT=>if pselect (K x) then VN (xi x-z) else 0.
  pose g:=fun x:UT=>if pselect (K x) then VN (xi x) else 0.
  pose h:=fun x:UT=>if pselect (K x) then VN z else 0.
  have hGOn:forall x,K x->g x=VN (xi x) by move=>x hx;rewrite /g;case:pselect.
  have hGOff:forall x,~K x->g x=0 by move=>x hx;rewrite /g;case:pselect.
  have hHOn:forall x,K x->h x=VN z by move=>x hx;rewrite /h;case:pselect.
  have hHOff:forall x,~K x->h x=0 by move=>x hx;rewrite /h;case:pselect.
  have hG:=(@real_subset_integral_total R UT gamma K (fun x=>VN (xi x))
    g a%:E hGOn hGOff).1 hA.
  have hH:=(@real_subset_integral_total R UT gamma K (fun _=>VN z)
    h b%:E hHOn hHOff).1 hB.
  have hSum:=@real_total_integral_add R UT gamma hGamma g h a b hG hH.
  have hFMeas:=@measurable_partial_real_embedding R UT gamma hGamma _
    (@measurable_total_cutoff R UT (real_line_metric R) gamma hGamma K
      (fun x=>VN (xi x-z)) 0 hKMeas hNorm).
  have hBound:forall x,`|f x|<=g x+h x.
    move=>x;rewrite /f /g /h;case:pselect=>hx.
    + rewrite (ger0_norm (real_seminorm_nonnegative hVN.1 _)).
      have hTriangle:=real_seminorm_triangle hVN.1 (xi x) (-z).
      by rewrite (real_seminorm_negate hVN.1 z) in hTriangle.
    + by rewrite normr0 addr0.
  have[c [hC _]]:=@real_total_dominated_integral R UT gamma hGamma f
    (fun x=>g x+h x) (a+b) hFMeas hSum hBound.
  exists c;apply:(@real_subset_integral_total R UT gamma K (fun x=>VN (xi x-z))
    f c%:E _ _).2 hC.
  + by move=>x hx;rewrite /f;case:pselect.
  + by move=>x hx;rewrite /f;case:pselect.
Qed.

(** Source for [current_open_density_constant_almost_agreement]:
    equality with a constant-density current forces
    almost equality of the original densities,
    supporting 4.1.26, p. 384. The only
    analytic input is the original local summability;
    neither density is assumed globally bounded. *)
Theorem current_open_density_constant_almost_agreement
    (T S:@current_space R h2 n U hU m):
  @is_current_integration_representation R h2 n m U hU T gamma xi->
  @is_current_integration_representation R h2 n m U hU S gamma (fun _=>z)->
  T=S->measure_almost_everywhere gamma [set x|xi x=z].
Proof.
move=>hT hS hEquality.
pose delta:=fun x:UT=>xi x-z.
pose hDelta:=current_open_density_subtract_constant_integrable.
pose Q:=@OpenCurrentDensity.value R h2 n m U hU gamma hGamma hRadon delta hDelta.
have hQ:=@OpenCurrentDensity.laws R h2 n m U hU gamma hGamma hRadon delta hDelta.
have hZero:Q=0.
  apply:(@current_values_extensional R h2 n m U hU)=>psi.
  pose a:=@current_test_value R h2 n U hU m psi.
  have hI:=@real_total_integral_subtract R UT gamma hGamma
    (fun x=>@MultivectorDual.evaluation R X m (xi x) (a (set_val x)))
    (fun x=>@MultivectorDual.evaluation R X m z (a (set_val x)))
    (@current_value R h2 n U hU m T psi)
    (@current_value R h2 n U hU m S psi)
    (distribution_representation_action hT psi) (distribution_representation_action hS psi).
  have hPairing:(fun x:UT=>@MultivectorDual.evaluation R X m (delta x) (a (set_val x)))=
      (fun x:UT=>@MultivectorDual.evaluation R X m (xi x) (a (set_val x))-
        @MultivectorDual.evaluation R X m z (a (set_val x))).
    apply:funext=>x;by rewrite !MultivectorDual.laws /delta /pairing linearB.
  rewrite hEquality subrr -hPairing in hI.
  have hValue:=EFin_inj (measure_integral_unique (distribution_representation_action hQ psi) hI).
  by rewrite linear0 hom_zeroE.
have hAlmost:=@current_open_density_zero_almost R h2 n m U hU gamma hGamma hRadon
  delta hDelta hZero.
apply:(@measure_almost_everywhere_mono R UT gamma hGamma _ _ _ hAlmost)=>x hx.
apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hx.
Qed.
End CurrentOpenDensityConstantAgreement.
