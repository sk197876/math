(** Actual-space endpoint regression for Federer (1969),
    4.1.14, pp. 371–372: the nonzero R^0
    unit point, constant endpoints zero and one,
    and the actual Lebesgue-AE differential majorant zero.
    Apply the final opaque affine-chain mass theorem.
    The original point variation integral equals one
    because the degree-zero power 0^0 is one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormDifferentialLinear NormClassOneUP NormClassZeroArithmetic
  NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanHomOperator
  LipschitzUP LipschitzBasic LipschitzConstant CurrentDomain CurrentSpaces
  CurrentDirac DiracCurrentBounds CurrentDiracRadonRepresentation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentMassSealed
  FlatCurrentsUP CurrentLipschitzCompactImage CurrentProperSupportDomain
  CurrentFlatLipschitzPushforwardSealed CurrentCompactLipschitzPushforwardSmooth
  CurrentCompactElementaryPushforwards CurrentFlatLipschitzMajorantVariation
  EuclideanLebesgueDimensions MeasureAlmostUP MeasureAlmostBasic
  CurrentCompactMajorantApproximationUP CurrentLipschitzAffineChainSealed
  CurrentLipschitzAffineChainMass SummableRealFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness PointMassIntegral
  MeasureDensity MeasurePushforward.
From FedererTests Require Import FlatCurrentEndpointExamples AffineCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LipschitzMajorantEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 0%N).
Local Notation Y:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation U:=(fun _:X=>True).
Local Notation V:=(fun _:Y=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hV:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation one:=(@euclidean_one_embed R 1).
Local Notation f:=(fun _:X=>(0:Y)).
Local Notation g:=(fun _:X=>one).
Local Notation sigma:=(fun _:X=>(0:R^o)).
Local Notation T:=(@dirac_current R h2 0%N U hU (0:X)).

(** Source for [lipschitz_majorant_constant_local]: the
    original constant maps satisfy the local Lipschitz
    hypothesis of Federer 4.1.14, p. 371,
    by the constant-map law of 2.2.7, p. 64. *)
Local Lemma lipschitz_majorant_constant_local (a:Y):
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U (fun _:X=>a).
Proof.
apply:metric_lipschitz_is_local.
exact:(metric_lipschitz_of_bound
  (least_metric_lipschitz_bound (@metric_lipschitz_constant_map R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U a))).
Qed.

(** Source for [lipschitz_majorant_actual_zero_graph]: the
    actual differential of each constant endpoint is
    the zero linear map, by 3.1.1, p. 209,
    verifying the original Lebesgue-AE graph premise
    of Federer 4.1.14, p. 371. *)
Local Lemma lipschitz_majorant_actual_zero_graph (a:Y):
  @is_current_ae_differential_majorant R 0%N 1%N U (fun _:X=>a) sigma.
Proof.
apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R 0%N)
  (euclidean_lebesgue_is_measure R 0%N) setT _ _
  (@measure_almost_everywhere_true R X (@euclidean_lebesgue_measure R 0%N)
    (euclidean_lebesgue_is_measure R 0%N)))=>x _ hx.
exists (0:Hom X Y);split.
- exact:(@norm_differential_constant R X Y NX NY hNX hNY U x a (hU x hx)).
- by rewrite (real_seminorm_zero (@euclidean_operator_norm_is_norm R 0%N 1%N).1).
Qed.

(** Source for [lipschitz_majorant_point_flat]: reuse the
    actual nonzero R^0 point's original singleton
    flat membership from 4.1.12, p. 368,
    for the final 4.1.14 mass regression. *)
Local Lemma lipschitz_majorant_point_flat:
  @is_flat_current R h2 0%N 0%N U hU T.
Proof.
exists (@flat_point_singleton_index R).
exact:(@zero_dimensional_point_flat R h2).
Qed.
Local Notation hFLocal:=(lipschitz_majorant_constant_local (0:Y)).
Local Notation hGLocal:=(lipschitz_majorant_constant_local one).
Local Notation hBand:=(fun (t:R) (x:X) (_:0<=t<= 1)
  (_:@current_support R h2 0%N U hU 0%N T x)=>Logic.I).
Local Notation chain:=(@CurrentLipschitzAffineChain.value R h2 0%N 1%N 0%N
  U V hU hV f g hFLocal hGLocal T lipschitz_majorant_point_flat hBand).

(** Source for [lipschitz_zero_majorant_point_affine_mass]:
    the final original mass bound of Federer
    4.1.14, pp. 371–372, gives mass at
    most one for the affine chain between
    two constant endpoint images of the nonzero
    R^0 point. The source variation is the
    proved unit point mass, and 0^0= 1. *)
Example lipschitz_zero_majorant_point_affine_mass:
  T<>0 /\(0:R)^+0%N= 1 /\
  (@CurrentMass.value R h2 1%N 1%N V hV chain<= 1%:E)%E.
Proof.
split;first exact:(@affine_zero_dimensional_point_nonzero R h2).
split;first by rewrite expr0.
pose hSigma:=@norm_class_zero_constant R X R^o NX (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R) U 0 hU.
pose hT:=@current_dirac_representable R h2 0%N U hU (0:X) Logic.I.
have hBound:=(@current_lipschitz_affine_chain_mass R h2 0%N 1%N 0%N
  U V hU hV f g (fun _ _=>Logic.I) (fun _ _=>Logic.I)
  hFLocal hGLocal sigma hSigma (lipschitz_majorant_actual_zero_graph (0:Y))
  (lipschitz_majorant_actual_zero_graph one) T lipschitz_majorant_point_flat
  (@dirac_current_finite_mass R h2 0%N U hU (0:X) Logic.I).2 hBand).2 hT.
rewrite (@current_dirac_variation R h2 0%N U hU (0:X) Logic.I hT) in hBound.
pose c:=@current_dirac_domain_point R 0%N U (0:X) Logic.I.
pose weight (x:current_domain R 0%N U):R:=
  NY (g (set_val x)-f (set_val x))*(0:R)^+0%N.
have hIntegral:=@point_mass_real_integral R (current_domain R 0%N U) c weight.
have hValue:=measure_lower_integral_unique
  (measure_lower_integral_specification _ (real_total_integrand weight))
  hIntegral.2.2.
change (measure_lower_integral (PointMassMeasure.point_mass R c)
  (real_total_integrand weight)=(NY (one-0)*(0:R)^+0%N)%:E) in hValue.
have hLength:NY (one-0)= 1.
  by rewrite subr0 euclidean_one_norm_coordinate
    /euclidean_one_embed ffunE normr1.
rewrite hValue hLength expr0 mulr1 in hBound.
exact:hBound.
Qed.

Local Notation pointImage:=(@CurrentFlatLipschitzPushforward.value R h2
  0%N 1%N 0%N U V hU hV g (fun _ _=>Logic.I) hGLocal
  T lipschitz_majorant_point_flat).

(** Source for [lipschitz_zero_majorant_point_variation]: the
    final all-set inequality of Federer 4.1.14,
    p. 371, applies to the actual global
    image of the nonzero R^0 point under
    the constant map to one. Its image
    is the original Dirac current, and its
    zero-degree density is 0^0= 1 for every
    source and target representation witness. *)
Example lipschitz_zero_majorant_point_variation:
  T<>0 /\pointImage=@dirac_current R h2 1%N V hV one /\
  @is_integration_representable_current R h2 0%N 0%N U hU T /\
  @is_integration_representable_current R h2 1%N 0%N V hV pointImage /\
  forall hSource:@is_integration_representable_current R h2 0%N 0%N U hU T,
    forall hTarget:@is_integration_representable_current R h2 1%N 0%N V hV pointImage,
      forall B,(@NormalisedCurrent.measure R h2 1%N 0%N V hV pointImage hTarget B<=
        measure_pushforward (@current_map_on_domain R 0%N 1%N U V g (fun _ _=>Logic.I))
          (measure_with_density (@NormalisedCurrent.measure R h2 0%N 0%N U hU T hSource)
            (real_total_integrand (fun _:current_domain R 0%N U=>((0:R)^+0%N)%R))) B)%E.
Proof.
split;first exact:(@affine_zero_dimensional_point_nonzero R h2).
split.
- pose K:=@flat_point_singleton_index R.
  pose hK:=@zero_dimensional_point_flat R h2.
  pose hg:=fun k=>@norm_class_constant R X Y NX NY hNX hNY U one k hU.
  rewrite (@CurrentFlatLipschitzPushforward.compact_value R h2 0%N 1%N 0%N
    U V hU hV g (fun _ _=>Logic.I) hGLocal T lipschitz_majorant_point_flat K hK).
  rewrite (@current_compact_lipschitz_pushforward_smooth R h2 0%N 1%N 0%N
    U V hU hV g (fun _ _=>Logic.I) hGLocal K T hK hg).
  exact:(@current_compact_map_dirac_image R h2 0%N 1%N U V hU hV
    g (fun _ _=>Logic.I) hg (0:X) Logic.I
    (@flat_supported_current_compact R h2 0%N 0%N U hU K T hK)).
- pose hSigma:=@norm_class_zero_constant R X R^o NX (fun t:R^o=>`|t|)
    (@scalar_absolute_value_norm R) U 0 hU.
  exact:(@current_flat_lipschitz_majorant_variation R h2 0%N 1%N 0%N
    U V hU hV g (fun _ _=>Logic.I) hGLocal T lipschitz_majorant_point_flat
    (@dirac_current_finite_mass R h2 0%N U hU (0:X) Logic.I).2
    sigma hSigma (lipschitz_majorant_actual_zero_graph one)).
Qed.
End LipschitzMajorantEndpointExamples.
