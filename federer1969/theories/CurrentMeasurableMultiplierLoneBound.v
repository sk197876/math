(** Federer (1969), 4.1.17, p. 374: original L1 coefficient
    approximation gives mass approximation of the actual measurable
    contraction. This supporting bound applies to the already sealed
    measurable multiplier of 4.1.7, pp. 355–356. Its finite coefficient
    bound and original all-test integral action suffice; neither
    coefficient is required smooth, bounded or compactly supported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP RealFunctionalNormUP
  NormMetric NormDifferentialUP NormBoundedBilinearUP VectorDaniellHypotheses
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing PairingLinear
  CurrentDomain CurrentSpaces CurrentEvaluation CurrentPointEvaluation CurrentCoefficientNorms
  CurrentDualNorm CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMeasurableMultiplierUP CurrentMeasurableMultiplierSealed
  CurrentMassUP CurrentMassSealed CurrentGlobalComassBound ExtendedSupremumUP
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralComparison SummableRealFunctionUP
  SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentMeasurableMultiplierLoneBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q p:nat.
Local Notation X := (R_n R n).
Local Notation Z := (fun d=>exterior_power X d).
Local Notation NZ := (fun d=>@current_vector_mass R h2 n d).
Local Notation NY := (@current_form_comass R h2 n p).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation C := (@current_space R h2 n U hU p).
Local Notation DT := (@current_test_space R h2 n U hU p).
Local Notation ev := (@current_test_value R h2 n U hU p).
Local Notation action := (@current_value R h2 n U hU p).
Local Notation M := (@CurrentMass.value R h2 n p U hU).
Variable V:lmodType R.
Variable NV:V->R.
Hypothesis hNV:is_real_norm NV.
Hypothesis hSep:is_separable_normed_space hNV.
Variable F:Z q->V->Z p.
Hypothesis hF:norm_bounded_bilinear (NZ q) NV (NZ p) F.
Variable T:@current_space R h2 n U hU q.
Hypothesis hT:@is_integration_representable_current R h2 n q U hU T.
Local Notation mu := (@NormalisedCurrent.measure R h2 n q U hU T hT).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n q U hU T hT).
Local Notation hNormal := (@NormalisedCurrent.laws R h2 n q U hU T hT).
Local Notation hm := (distribution_representation_measure
  (normalised_distribution_representation_laws hNormal)).
Local Notation field := (is_locally_summable_current_field hNV mu).
Local Notation product f hf := (@CurrentMeasurableMultiplier.value R h2 n q p
  U hU V NV hNV hSep F hF T hT f hf).

(** Source for [current_measurable_multiplier_lone_bound]: a single
    finite coefficient constant bounds the mass difference of the
    original multiplier currents by the original L1 coefficient
    error, supporting Federer 4.1.17, p. 374, through 4.1.7,
    pp. 355–356. Local summability is enough for each coefficient;
    only their difference has a finite global norm integral. *)
Theorem current_measurable_multiplier_lone_bound:
  exists D:R,0<=D /\
  forall (f g:UT->V) (hf:field f) (hg:field g) a,
    is_measure_integral mu (real_total_integrand
      (fun x=>NV (f x-g x))) a%:E->
    (M (product f hf-product g hg)<=(D*a)%:E)%E.
Proof.
have[D [hD hBound]]:=hF.2.
exists D;split;first exact:hD.
move=>f g hf hg a hError.
pose A:=product f hf.
pose B:=product g hg.
have hUnit x:NZ q (eta x)<=1:=
  normalised_distribution_density_unit_bound hNormal x.
have hScaled:=@real_total_integral_scale R UT mu hm
  (fun x=>NV (f x-g x)) a D hError.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n p U hU (A-B)))
  =>b [psi [hPsi <-]].
pose u:=fun x:UT=>pairing (F (eta x) (f x)) (ev psi (set_val x)).
pose v:=fun x:UT=>pairing (F (eta x) (g x)) (ev psi (set_val x)).
have hA:=(@CurrentMeasurableMultiplier.laws R h2 n q p U hU V NV
  hNV hSep F hF T hT f hf).1 psi.
have hB:=(@CurrentMeasurableMultiplier.laws R h2 n q p U hU V NV
  hNV hSep F hF T hT g hg).1 psi.
have hDifference:=@real_total_integral_subtract R UT mu hm u v
  (action A psi) (action B psi) hA hB.
have hPoint x:u x-v x<=D*NV (f x-g x).
  pose z:=F (eta x) (f x-g x).
  pose w:=ev psi (set_val x).
  have hIdentity:u x-v x=pairing z w.
    rewrite /u /v /z /w (linB (hF.1.2 (eta x)))
      (linB ((@pairing_bilinear R X R^o p).1 (ev psi (set_val x)))).
    by [].
  have hPair:=real_functional_norm_bound
    (@current_mass_pairing_norm R h2 n p z) w.
  have hTest:NY w<=1.
    exact:((@current_global_comass_bound R h2 n p U (ev psi) 1).1
      hPsi (set_val x) (set_valP x)).
  have hPairUpper:NZ p z*NY w<=NZ p z.
    have h:=ler_wpM2l
      (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n p).1 z)
      hTest.
    by rewrite mulr1 in h.
  have hCoefficient:NZ q (eta x)*NV (f x-g x)<=NV (f x-g x).
    have h:=ler_wpM2r (real_seminorm_nonnegative hNV.1 (f x-g x)) (hUnit x).
    by rewrite mul1r in h.
  rewrite hIdentity.
  apply:(le_trans (ler_norm _)).
  apply:(le_trans hPair).
  apply:(le_trans hPairUpper).
  apply:(le_trans (hBound (eta x) (f x-g x))).
  exact (ler_wpM2l hD hCoefficient).
have hOrder:measure_almost_everywhere mu
    (partial_extended_le_locus
      (real_total_integrand (fun x=>u x-v x))
      (real_total_integrand (fun x=>D*NV (f x-g x)))).
  apply:(@measure_almost_everywhere_mono R UT mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _.
  exists (u x-v x)%:E,(D*NV (f x-g x))%:E.
  split;first by rewrite real_total_integrand_graph.
  split;first by rewrite real_total_integrand_graph.
  rewrite lee_fin;exact:hPoint.
have hCompare:=measure_integral_monotone hm hDifference hScaled hOrder.
pose evaluation:=@current_point_evaluation R h2 n p U hU psi.
have hValue:action (A-B) psi=action A psi-action B psi.
  exact:(linB (hom_linear evaluation) A B).
rewrite hValue;exact:hCompare.
Qed.
End CurrentMeasurableMultiplierLoneBound.
