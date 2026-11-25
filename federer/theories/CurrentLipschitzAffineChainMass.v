(** Federer (1969), 4.1.14, pp. 371–372: the
    original affine-chain mass bound for every finite-mass
    compact flat current. The common continuous majorant
    bounds the actual endpoint differentials Lebesgue almost
    everywhere on U. Derive all source neighbourhoods,
    compact indices, representations and smooth families;
    the conclusion retains the literal variation integral on U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroTopology NormScalarClassZeroTopology NormClassHigherRestriction
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates LipschitzUP OpenLocalLipschitzCompact
  SmoothCompactSet CurrentDomain MetricSubsetBackground
  CurrentSpaces CurrentMassSealed CurrentFiniteMassRepresentation
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOpenRestriction
  CurrentOpenRestrictionMass CurrentOpenRestrictionVariation
  CurrentFlatSupportNeighbourhoodRestriction CurrentFlatOpenRestriction
  CurrentApproximationOpenRestriction
  CurrentLipschitzCompactImage FlatCurrentsUP FlatCurrentFinite
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass CurrentAffineHomotopyLocalLipschitz
  CurrentCompactTimeCylinder CurrentFlatTimeCylinder
  CurrentCompactMajorantApproximationUP CurrentAEMajorantRestriction
  CurrentAffineMajorantApproximationUP CurrentAffineMajorantApproximationExistence
  CurrentAffineMajorantImageMass CurrentAffineWeightContinuity
  CurrentLipschitzAffineChainUP CurrentLipschitzAffineChainSealed
  CurrentLipschitzAffineNeighbourhood CurrentLipschitzAffineChainRestrictedValue
  CurrentFlatLipschitzPushforwardSealed CurrentNeighbourhoodContinuousWeightIntegral
  SummableRealFunctionUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzAffineChainMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypotheses (hFImage:forall x,U x->V (f x)) (hGImage:forall x,U x->V (g x)).
Hypotheses (hFLocal:@is_locally_metric_lipschitz R XT YT U f)
  (hGLocal:@is_locally_metric_lipschitz R XT YT U g).
Variable sigma:X->R^o.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Hypotheses (hFMajorant:@is_current_ae_differential_majorant R n nu U f sigma)
  (hGMajorant:@is_current_ae_differential_majorant R n nu U g sigma).
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Hypothesis hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
  V ((1-t)*:f x+t*:g x).
Local Notation Q := (@CurrentLipschitzAffineChain.value R h2 n nu m U V hU hV
  f g hFLocal hGLocal T hFlat hBand).

(** Source for [current_lipschitz_affine_chain_mass]: the original
    M(h#([0,1] times T)) <= ||T||(|g-f|sigma^m), Federer
    4.1.14, p. 371. The affine map need take
    values in V only over the segments above spt T.
    T is any finite-mass flat current. No normality,
    representation, smoothing-family or neighbourhood premise is added. *)
Theorem current_lipschitz_affine_chain_mass :
  @is_integration_representable_current R h2 n m U hU T /\
  forall hT:@is_integration_representable_current R h2 n m U hU T,
    (@CurrentMass.value R h2 nu (1+m)%N V hV Q<=
      measure_lower_integral (@NormalisedCurrent.measure R h2 n m U hU T hT)
        (real_total_integrand (fun x:current_domain R n U=>
          (NY (g (set_val x)-f (set_val x))*(sigma (set_val x))^+m)%R)))%E.
Proof.
split;first exact:(@current_finite_mass_representation R h2 n m U hU T hFinite).
move=>hT.
have[A0 [hA0 [W0 [hW0 [hW0U [hSupport0 hBand0]]]]]]:=
  @current_lipschitz_affine_neighbourhood_exists R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand.
pose S0:=@current_open_restriction R h2 n m W0 U hW0 hU hW0U T.
have[L [hL _]]:=@flat_current_support_neighbourhood_restriction_indexed
  R h2 n m U W0 hU hW0 hW0U T hFlat hSupport0.
have hS0Finite:(@CurrentMass.value R h2 n m W0 hW0 S0< +oo)%E.
  exact:le_lt_trans (@current_open_restriction_mass_bound R h2 n m W0 U
    hW0 hU hW0U T) hFinite.
have hS0Compact:=@flat_supported_current_compact R h2 n m W0 hW0 L S0 hL.
pose hS0:=@current_neighbourhood_restriction_representable R h2 n m W0 U
  hW0 hU hW0U T hT hSupport0.
pose hF0:=@metric_local_lipschitz_domain_restriction R XT YT U W0 f hW0U hFLocal.
pose hG0:=@metric_local_lipschitz_domain_restriction R XT YT U W0 g hW0U hGLocal.
pose hFImage0:=fun x (hx:W0 x)=>@hFImage x (@hW0U x hx).
pose hGImage0:=fun x (hx:W0 x)=>@hGImage x (@hW0U x hx).
pose hSigma0:=@norm_class_zero_open_restriction R X R^o NX (fun t:R^o=>`|t|)
  U W0 sigma hW0U hW0 hSigma.
pose hFMajorant0:=@current_ae_differential_majorant_open_restriction
  R n nu U W0 hW0 hW0U f sigma hFMajorant.
pose hGMajorant0:=@current_ae_differential_majorant_open_restriction
  R n nu U W0 hW0 hW0U g sigma hGMajorant.
have hBandL:forall t x,0<=t<=1->smooth_compact_carrier L x->
    V ((1-t)*:f x+t*:g x).
  move=>t x ht hx;exact:@hBand0 t x
    (@current_homotopy_closed_time_band R A0 hA0 t ht)
    (smooth_compact_in_domain L x hx).
have[A [W1 [a [b [eta hData]]]]]:=
  @current_affine_majorant_approximation_exists R n nu W0 V hW0 hV f g
    hFImage0 hGImage0 hF0 hG0 L sigma hSigma0 hFMajorant0 hGMajorant0 hBandL.
pose hA:=current_affine_majorant_parameter hData.
pose hW1:=current_affine_majorant_domain_open hData.
pose hW1W0:=current_affine_majorant_domain_in_domain hData.
pose hL1:=current_affine_majorant_domain_contains hData.
pose L1:=@current_compact_index_in_open R n W0 W1 L hL1.
pose S1:=@current_open_restriction R h2 n m W1 W0 hW1 hW0 hW1W0 S0.
have hS1Flat:=@flat_current_open_restriction R h2 n m W0 W1 hW0 hW1
  hW1W0 L hL1 S0 hL.
have hS1Finite:(@CurrentMass.value R h2 n m W1 hW1 S1< +oo)%E.
  exact:le_lt_trans (@current_open_restriction_mass_bound R h2 n m W1 W0
    hW1 hW0 hW1W0 S0) hS0Finite.
have hSupport1:@current_support R h2 n W0 hW0 m S0 `<=` W1.
  move=>x hx;exact:@hL1 x (@flat_current_supported_support R h2 n m W0 hW0 L S0 hL x hx).
pose hS1:=@current_neighbourhood_restriction_representable R h2 n m W1 W0
  hW1 hW0 hW1W0 S0 hS0 hSupport1.
pose hFClass0:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY W0 f hW0 hF0.
pose hGClass0:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY W0 g hW0 hG0.
pose hFClass1:=@norm_class_zero_open_restriction R X Y NX NY W0 W1 f hW1W0 hW1 hFClass0.
pose hGClass1:=@norm_class_zero_open_restriction R X Y NX NY W0 W1 g hW1W0 hW1 hGClass0.
pose hSigma1:=@norm_class_zero_open_restriction R X R^o NX (fun t:R^o=>`|t|)
  W0 W1 sigma hW1W0 hW1 hSigma0.
pose hF1:=@metric_local_lipschitz_domain_restriction R XT YT W0 W1 f hW1W0 hF0.
pose hG1:=@metric_local_lipschitz_domain_restriction R XT YT W0 W1 g hW1W0 hG0.
pose H:=@CurrentAffineHomotopy.value R n nu f g.
pose AT:=@current_homotopy_time_domain R A.
pose hAT:=@current_homotopy_time_domain_open R A hA.
pose AW:=@current_homotopy_product_domain R n A W1.
pose hAW:=@current_cartesian_domain_open R 1%N n AT W1 hAT hW1.
pose hHImage:=current_affine_majorant_original_image hData.
pose hHLocal:=@current_affine_homotopy_locally_lipschitz R n nu f g A hA W1 hW1 hF1 hG1.
pose KP:=@current_compact_time_cylinder R n A W1 hA L1.
pose P:=@CartesianCurrentProduct.value R h2 1%N n 1%N m AT W1 hAT hW1
  (@current_homotopy_time_segment R A hA h2) S1.
pose hPFlat:=@flat_current_time_cylinder R h2 n m A W1 hA hW1 L1 S1 hS1Flat.
have hPGlobal:@is_flat_current R h2 (1+n)%N (1+m)%N AW hAW P by exists KP.
have hBand1:forall t x,A t->W1 x->V ((1-t)*:f x+t*:g x).
  move=>t x ht hx.
  have hImage:=@hHImage (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))
    (@current_homotopy_join_member R n A W1 t x ht hx).
  by rewrite CurrentAffineHomotopy.laws in hImage.
have hQEquality:=@current_lipschitz_affine_chain_restricted_value R h2 n nu m
  U V hU hV f g hFLocal hGLocal T hFlat Q
  (@CurrentLipschitzAffineChain.laws R h2 n nu m U V hU hV
    f g hFLocal hGLocal T hFlat hBand) W0 hW0 hW0U hSupport0 A hA W1 hW1
  hW1W0 hSupport1 hBand1 hHImage hHLocal hPGlobal.
have hQPoint:=(@CurrentFlatLipschitzPushforward.laws R h2 (1+n)%N nu (1+m)%N
  AW V hAW hV H hHImage hHLocal P hPGlobal).2 KP hPFlat.
rewrite -hQEquality in hQPoint.
have hBound:=(@current_affine_majorant_image_mass R h2 n nu m W0 V hV L f g sigma
  A W1 a b eta hData hHLocal hFClass1 hGClass1 hSigma1 S1 hS1Flat hS1Finite Q hQPoint).2 hS1.
pose Weight (x:X):R^o:=NY (g x-f x)*(sigma x)^+m.
pose F0 (x:current_domain R n W0):R^o:=Weight (set_val x).
pose FU (x:current_domain R n U):R^o:=Weight (set_val x).
have hF0Continuous:continuous F0.
  exact:(@current_affine_weight_continuous R (metric_subset (W0:set XT)) Y NY hNY
    (fun x=>f (set_val x)) (fun x=>g (set_val x)) (fun x=>sigma (set_val x)) m
    (@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY W0 f hFClass0)
    (@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY W0 g hGClass0)
    (@norm_class_zero_scalar_restriction_continuous R X NX hNX W0 sigma hSigma0)).
pose hFClassU:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hFLocal.
pose hGClassU:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U g hU hGLocal.
have hFUContinuous:continuous FU.
  exact:(@current_affine_weight_continuous R (metric_subset (U:set XT)) Y NY hNY
    (fun x=>f (set_val x)) (fun x=>g (set_val x)) (fun x=>sigma (set_val x)) m
    (@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U f hFClassU)
    (@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U g hGClassU)
    (@norm_class_zero_scalar_restriction_continuous R X NX hNX U sigma hSigma)).
have hValue1:=@current_neighbourhood_continuous_weight_lower_value R h2 n m W1 W0
  hW1 hW0 hW1W0 S0 hS0 hSupport1 hS1 hS0Finite hS0Compact F0 hF0Continuous.
have[K hK]:=hFlat.
have hCompact:=@flat_supported_current_compact R h2 n m U hU K T hK.
have hValue0:=@current_neighbourhood_continuous_weight_lower_value R h2 n m W0 U
  hW0 hU hW0U T hT hSupport0 hS0 hFinite hCompact FU hFUContinuous.
change (measure_lower_integral (@NormalisedCurrent.measure R h2 n m W1 hW1 S1 hS1)
    (real_total_integrand (fun x:current_domain R n W1=>Weight (set_val x)))=
  measure_lower_integral (@NormalisedCurrent.measure R h2 n m W0 hW0 S0 hS0)
    (real_total_integrand F0)) in hValue1.
change (measure_lower_integral (@NormalisedCurrent.measure R h2 n m W0 hW0 S0 hS0)
    (real_total_integrand F0)=
  measure_lower_integral (@NormalisedCurrent.measure R h2 n m U hU T hT)
    (real_total_integrand FU)) in hValue0.
rewrite hValue1 hValue0 in hBound.
exact:hBound.
Qed.
End CurrentLipschitzAffineChainMass.
