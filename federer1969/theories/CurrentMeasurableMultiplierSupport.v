(** Federer (1969), 4.1.7, pp. 355–356, 359:
    a measurable contraction or vector product
    has support contained in the original
    current support. This supporting locality law
    uses the actual integral action and the
    proved nullness of annihilation open sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import LatticeL1ApproximationLaws Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingIsomorphism AlternatingPairing
  CurrentDomain CurrentCoefficientNorms CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierSealed CurrentRadonAnnihilation
  CurrentSupportGeometry NormBoundedBilinearUP VectorDaniellHypotheses FunctionalSupportUP SmoothFunctionSupport
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureIntegralUniqueness SummableRealFunctionUP DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentMeasurableMultiplierSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Variable V:lmodType R.
Variable NV:V->R.
Hypothesis hNV:is_real_norm NV.
Hypothesis hSep:is_separable_normed_space hNV.
Variable F:exterior_power X q->V->exterior_power X p.
Hypothesis hF:norm_bounded_bilinear (@current_vector_mass R h2 n q) NV
  (@current_vector_mass R h2 n p) F.
Variable T:@current_space R h2 n U hU q.
Hypothesis hT:@is_integration_representable_current R h2 n q U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n q U hU T hT).
Local Notation hRepresentation := (@NormalisedCurrent.laws R h2 n q U hU T hT).
Let hm:=distribution_representation_measure (normalised_distribution_representation_laws hRepresentation).
Variable f:UT->V.
Hypothesis hField:is_locally_summable_current_field hNV mu f.
Local Notation S := (@CurrentMeasurableMultiplier.value R h2 n q p U hU V NV hNV hSep F hF T hT f hField).

(** Source for [current_measurable_multiplier_support_subset]:
    the actual measurable product's support lies
    in spt T, supporting proper pushforward
    of Baire contractions in Federer 4.1.7,
    p. 359. No continuity or finite
    total mass of the multiplier is imposed. *)
Theorem current_measurable_multiplier_support_subset:
  @current_support R h2 n U hU p S `<=` @current_support R h2 n U hU q T.
Proof.
move=>x hx;split;first exact:hx.1.
move=>[W [[hW hAnnihilation] hWx]].
apply:hx.2;exists W;split;last exact:hWx.
split;first exact:hW.
move=>psi hPsi.
have hNull:=@current_radon_annihilation_null R h2 n q U hU T hT W (conj hW hAnnihilation).
have hOutside:measure_almost_everywhere mu (~` (set_val @^-1` W:set UT)).
  by rewrite /measure_almost_everywhere setCK.
have hOriginal:=(@CurrentMeasurableMultiplier.laws R h2 n q p U hU V NV hNV hSep F hF T hT
  f hField).1 psi.
have hEqual:measure_almost_equal mu
    (real_total_integrand (fun z=>pairing
      (F (@NormalisedCurrent.auxiliary_density R h2 n q U hU T hT z) (f z))
      (@current_test_value R h2 n U hU p psi (set_val z)))) (real_total_integrand (fun _=>0)).
  apply:(@measure_almost_everywhere_mono R UT mu hm _ _ _ hOutside)=>z hz.
  have hZero:@current_test_value R h2 n U hU p psi (set_val z)=0.
    apply:contrapT=>hNonzero;apply:hz;apply:hPsi.
    split;first exact:set_valP z.
    exact:(@subset_closure (real_norm_metric_space hNX) _ (set_val z) hNonzero).
  exists (0:R)%:E;split;rewrite real_total_integrand_graph;last by [].
  by rewrite hZero /pairing linear0 hom_zeroE.
have hValue:=measure_integral_unique (measure_integral_almost_equal hm hOriginal hEqual)
  (@real_total_zero_integral R UT mu hm).
exact:EFin_inj hValue.
Qed.
End CurrentMeasurableMultiplierSupport.
