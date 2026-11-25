(** Federer (1969), 4.1.14, p. 371: weighted variation
    bounds pass from the smooth images to their weak limit.
    This supporting form uses only the original test action,
    the finite-gauge criterion of 4.1.5, pp. 349–350, and
    Radon comparison on every set. A representation of the
    limit is proved, not required as an extra premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms CurrentDomain CurrentCoefficientNorms
  CurrentSpaces CurrentWeakSequenceLimit CurrentIntegrationCriterion
  NormalisedCurrentSealed SmoothFunctionSpaceUP SmoothTestSpaces
  SmoothTestEvaluation DistributionVariationDomain DistributionVariationUP
  DistributionVariationBasic DistributionFiniteGaugeBound DistributionFiniteVariationUP
  FunctionLatticeUP CompactSupportFunctionUP RealIntegralFunctionalUP
  RadonCompactScalarIntegral RadonPositiveCompactComparison
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  MeasureUP RadonMeasureUP MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentWeakCompactTestBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation A:=(A_m X R^o m).
Local Notation AN:=(@current_form_comass R h2 n m).
Local Notation hAN:=(@current_form_comass_real_norm R h2 n m).
Local Notation DV:=(@current_test_space R h2 n U hU m).
Local Notation hE:=(@current_smooth_space_laws R h2 n U hU m).
Local Notation dvalues:=(@distribution_domain_values R
  (real_norm_metric_space hNX) U A DV (smooth_test_values_hom hE)).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation action:=(@current_value R h2 n U hU m).
Local Notation Kplus:=(positive_function_lattice
  (@compactly_supported_continuous_functions R UT)).
Variables (u:nat->C) (Q:C).
Hypothesis hWeak:@is_current_weak_sequence_limit R h2 n m U hU u Q.
Variable nu:set UT->\bar R.
Hypotheses (hn:is_measure nu) (hr:is_radon_measure nu).
Local Notation F:=(@radon_positive_compact_integral R UT nu hn hr).
Hypothesis hBounds:forall h,Kplus h->exists b:nat->R,
  (forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|b i-F h|<eps) /\
  (forall i,forall phi:DV,(forall x,AN (dvalues phi x)<=h x)->action (u i) phi<=b i).

(** Source for [current_weak_limit_compact_test_bound]:
    the original scalar bound passes to the actual weak
    limit in Federer 4.1.14, p. 371. Both convergences
    are used at a common sequence index. *)
Theorem current_weak_limit_compact_test_bound h:
  Kplus h->forall phi:DV,(forall x,AN (dvalues phi x)<=h x)->action Q phi<=F h.
Proof.
move=>hH phi hPhi.
have [b [hLimit hBound]]:=@hBounds h hH.
apply/ler_addgt0Pr=>eps hEps.
have hHalf:0<eps/2 by lra.
have [N hN]:=hLimit _ hHalf.
have [M hM]:=@hWeak phi (eps/2) hHalf.
have hNClose:=hN (maxn N M) (leq_maxl N M).
have hMClose:=hM (maxn N M) (leq_maxr N M).
have hB:=hBound (maxn N M) phi hPhi.
move:hMClose;rewrite ltr_norml=>/andP[hMLow hMHigh].
move:hNClose;rewrite ltr_norml=>/andP[hNLow hNHigh].
lra.
Qed.

(** Source for [current_weak_limit_compact_bounds_representable]:
    finite positive compact scalar bounds give the original
    integration representation of the limit, supporting Federer
    4.1.14, p. 371, by 4.1.5, pp. 349–350. No prior
    representation or normality of the limit is required. *)
Theorem current_weak_limit_compact_bounds_representable:
  @is_integration_representable_current R h2 n m U hU Q.
Proof.
apply:(@current_integration_finite_gauge_criterion R h2 n m U hU Q).1=>h hH.
have [b [hB _]]:=@distribution_finite_gauge_from_test_bound R UT A AN hAN
  DV dvalues (action Q) h (F h) hH.2 (current_weak_limit_compact_test_bound hH).
by exists b.
Qed.

(** Source for [current_weak_limit_compact_bounds_variation]:
    the weighted variation inequality of Federer 4.1.14,
    p. 371, holds on every outer set. Comparison of the
    original positive compact integrals proves this; no
    measurability or finite mass of the target set is added. *)
Theorem current_weak_limit_compact_bounds_variation
    (hQ:@is_integration_representable_current R h2 n m U hU Q):
  forall B,(@NormalisedCurrent.measure R h2 n m U hU Q hQ B<=nu B)%E.
Proof.
pose rho:=@NormalisedCurrent.measure R h2 n m U hU Q hQ.
have hR:=@NormalisedCurrent.laws R h2 n m U hU Q hQ.
have hBase:=normalised_distribution_representation_laws hR.
have hRho:=distribution_representation_measure hBase.
have hRadon:=distribution_representation_radon hBase.
pose G:=@radon_positive_compact_integral R UT rho hRho hRadon.
have hG:=@radon_positive_compact_integral_laws R UT rho hRho hRadon.
have hF:=@radon_positive_compact_integral_laws R UT nu hn hr.
apply:(@radon_positive_compact_integral_comparison R UT rho nu
  hRho hn hRadon hr G F hG hF)=>h hH.
have [b [hGauge hIntegral]]:=normalised_distribution_original_gauge hR hH.
have hEqual:=measure_integral_unique hIntegral (hG h hH).
have hBound:=@distribution_variation_least_finite_bound R UT A AN DV
  dvalues (action Q) h b%:E (F h) hGauge
  (current_weak_limit_compact_test_bound hH).
rewrite hEqual lee_fin in hBound;exact:hBound.
Qed.
End CurrentWeakCompactTestBounds.
