(** Actual-space regressions supporting Federer (1969), 4.1.9,
    pp. 363–364: an unbounded time interval, a nonzero
    zero-dimensional source current, its stationary deformation
    of mass zero, and both scalar power endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanHomOperator CurrentMapDifferential CurrentDomain CurrentSpaces CurrentCoefficientNorms
  SmoothCompactSet CurrentSupportGeometry CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeVelocity CurrentAffineHomotopyDifferential CurrentHomotopyCompactCylinder
  CurrentDeformationChainSealed CurrentHomotopyCylinder CurrentAffineHomotopyMass HomotopyAffinePowerFields
  CurrentIntegrationCriterion NormalisedCurrentSealed DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  EuclideanFundamentalCurrent EuclideanFundamentalCurrentVariation EuclideanFundamentalCurrentNonzero
  CurrentMassSealed CurrentMassBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureConullZeroIntegral
  MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP ScalarAffinePowerMoment
  LebesgueScalarMeasure MeasureSubsetIntegral RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HomotopyCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation Z := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation U := (fun _:X=>True).
Local Notation A := (fun _:R=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation f := (fun _:X=>(0:X)).
Local Notation h := (fun _:Z=>(0:X)).

(** Source for [whole_line_homotopy_interval]: the original
    open time interval may be unbounded, checking the
    literal hypotheses of Federer 4.1.9, p. 363. *)
Lemma whole_line_homotopy_interval:@is_homotopy_parameter_interval R A.
Proof. constructor;first exact:openT;by []. Qed.

(** Source for [zero_dimensional_stationary_smooth]: the
    actual constant homotopy is smooth on its original
    product domain, checking Federer 4.1.9, p. 363,
    in source and target dimension zero. *)
Lemma zero_dimensional_stationary_smooth:
  @norm_class_all_orders R Z X NZ NX hNZ hNX
    (@current_homotopy_product_domain R 0%N A U) h.
Proof.
move=>k;apply:(@norm_class_constant R Z X NZ NX hNZ hNX
  (@current_homotopy_product_domain R 0%N A U) 0 k).
move=>z hz;exists 1;split;first exact:ltr01;by [].
Qed.

(** Source for [zero_dimensional_stationary_homotopy]: an
    actual smooth stationary homotopy on R^0 with
    time domain R, checking the original domain
    and regularity hypotheses of Federer 4.1.9, p. 363.
    Proof-index transport below identifies the original
    E^0 with the source carrier of this homotopy. *)
Definition zero_dimensional_stationary_homotopy:
  @is_smooth_current_homotopy R 0%N 0%N A U U f f h:=
  conj (@Build_is_current_homotopy_geometry R 0%N 0%N A U U f f h
    whole_line_homotopy_interval hFull hFull
    (fun _ _=>Logic.I)
    (fun (x:X) (_:True)=>erefl (0:X))
    (fun (x:X) (_:True)=>erefl (0:X)))
    zero_dimensional_stationary_smooth.
Local Notation hH := zero_dimensional_stationary_homotopy.
Local Notation OpenU := (forall x:X,U x->norm_domain_interior NX U x).
Local Notation E0 := (@euclidean_fundamental_current R h2 0%N).
Local Notation hSource := (@current_homotopy_source_open R 0%N 0%N A U U f f h hH.1).
Local Notation hTarget := (@current_homotopy_target_open R 0%N 0%N A U U f f h hH.1).

(** Source for [zero_dimensional_euclidean_current]: the
    original E^0 of Federer 4.1.7, p. 357,
    used in 4.1.9, pp. 363–364. Transport along
    equality of the openness proofs changes only
    the proof index of the actual current space. *)
Definition zero_dimensional_euclidean_current (hu:OpenU):
  @current_space R h2 0%N U hu 0%N:=
  @eq_rect OpenU hFull (fun hp=>@current_space R h2 0%N U hp 0%N)
    E0 hu (Prop_irrelevance hFull hu).

(** Source for [zero_dimensional_euclidean_current_full]:
    the transported current is the original E^0
    on its original whole-space carrier, supporting
    Federer 4.1.7, p. 357, and 4.1.9,
    pp. 363–364. *)
Lemma zero_dimensional_euclidean_current_full:
  zero_dimensional_euclidean_current hFull=E0.
Proof.
rewrite /zero_dimensional_euclidean_current.
have he:(Prop_irrelevance hFull hFull)=erefl hFull:=Prop_irrelevance _ _.
by rewrite he.
Qed.

(** Source for [zero_dimensional_euclidean_current_nonzero]:
    the actual E^0 remains nonzero under proof-index
    transport, using Federer 4.1.7, p. 357,
    in the case of 4.1.9, pp. 363–364. *)
Lemma zero_dimensional_euclidean_current_nonzero (hu:OpenU):
  zero_dimensional_euclidean_current hu<>0.
Proof.
have ->:hu=hFull:=Prop_irrelevance _ _.
rewrite zero_dimensional_euclidean_current_full.
exact:euclidean_fundamental_current_nonzero.
Qed.

(** Source for [zero_dimensional_euclidean_current_representable]:
    the original integration representation of E^0
    is preserved by equality of openness proofs,
    supporting Federer 4.1.7, pp. 357–358,
    in the affine estimate of 4.1.9, p. 364. *)
Lemma zero_dimensional_euclidean_current_representable (hu:OpenU):
  @is_integration_representable_current R h2 0%N 0%N U hu
    (zero_dimensional_euclidean_current hu).
Proof.
have ->:hu=hFull:=Prop_irrelevance _ _.
rewrite zero_dimensional_euclidean_current_full.
exact:euclidean_fundamental_current_representable.
Qed.
Local Notation T := (zero_dimensional_euclidean_current hSource).
Local Notation hT := (zero_dimensional_euclidean_current_representable hSource).

(** Source for [zero_dimensional_homotopy_source_nonzero]: the
    actual source in this homotopy regression is nonzero
    E^0, using Federer 4.1.7, p. 357, in
    the degree-zero case of 4.1.9, pp. 363–364. *)
Example zero_dimensional_homotopy_source_nonzero:T<>0.
Proof. exact:zero_dimensional_euclidean_current_nonzero. Qed.

(** Source for [zero_dimensional_homotopy_support_compact]: the
    actual nonzero E^0 source has compact support,
    checking that the original cylinder properness in
    Federer 4.1.9, p. 363, is satisfied. *)
Lemma zero_dimensional_homotopy_support_compact:
  @compact (real_norm_metric_space hNX) (@current_support R h2 0%N U hSource 0%N T).
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX U [set (0:X)] (fun _ _=>Logic.I) (@compact_set1 (real_norm_metric_space hNX) (0:X)).
apply:(@current_support_compact_bound R h2 0%N 0%N U hSource K T)=>x hx.
change (x=0);exact:(@coordinate_zero R x).
Qed.
Local Notation hp := (@current_homotopy_compact_support_proper R h2 0%N 0%N 0%N
  A U U f f h hH T zero_dimensional_homotopy_support_compact).
Local Notation chain := (@CurrentDeformationChain.value R h2 0%N 0%N 0%N A U U f f h hH T hp).

(** Source for [zero_dimensional_stationary_velocity]: the
    actual original velocity of the R^0 stationary
    homotopy is zero, checking the affine identity
    of Federer 4.1.9, p. 364. *)
Example zero_dimensional_stationary_velocity t (x:X):
  @current_homotopy_time_velocity R 0%N 0%N A U h t x=0.
Proof.
have hAffine s y:A s->U y->@current_homotopy_slice_map R 0%N 0%N h s y=(1-s)*:f y+s*:f y.
  by move=>_ _;rewrite !scaler0 add0r.
have hVelocity:=@current_affine_homotopy_time_velocity R 0%N 0%N A U U f f h hH hAffine t x Logic.I Logic.I.
by rewrite subrr in hVelocity.
Qed.

(** Source for [zero_dimensional_stationary_chain_mass]: the
    deformation of the actual nonzero E^0 source by
    the stationary affine homotopy has mass zero,
    checking the full original estimate in Federer
    4.1.9, p. 364. The proof uses the proved
    mass estimate and the original integral uniqueness. *)
Example zero_dimensional_stationary_chain_mass:
  @CurrentMass.value R h2 0%N 1%N U hTarget chain=0%E.
Proof.
have hAffine s y:A s->U y->@current_homotopy_slice_map R 0%N 0%N h s y=(1-s)*:f y+s*:f y.
  by move=>_ _;rewrite !scaler0 add0r.
have[_ [hMean [_ [hMass _]]]]:=@current_affine_homotopy_mass_estimates R h2 0%N 0%N 0%N
  A U U f f h hH T hT hAffine hp.
pose beta:=@NormalisedCurrent.measure R h2 0%N 0%N U hSource T hT.
pose hBeta:=distribution_representation_measure
  (normalised_distribution_representation_laws (@NormalisedCurrent.laws R h2 0%N 0%N U hSource T hT)).
pose a:=fun x:current_domain R 0%N U=>NX (f (set_val x)-f (set_val x)).
pose b:=fun x:current_domain R 0%N U=>@euclidean_operator_norm R 0%N 0%N
  (@current_map_differential R 0%N 0%N U f (set_val x)).
pose mean:=@homotopy_affine_power_mean R 0%N 0%N U a b b.
have hZero:is_measure_integral beta (real_total_integrand mean) 0%E.
  apply:(@measure_almost_zero_integral R (current_domain R 0%N U) beta hBeta).
  apply:(@measure_almost_everywhere_mono R (current_domain R 0%N U) beta hBeta setT _ _
    (measure_almost_everywhere_true hBeta))=>x _.
  exists (0:R);split;last by [].
  change (mean x=0).
  by rewrite /mean /homotopy_affine_power_mean /a subrr inner_norm0 mul0r.
have hValue:=measure_integral_unique hMean hZero.
rewrite hValue in hMass.
apply/eqP;rewrite eq_le;apply/andP;split;first exact:hMass.
exact:current_mass_nonnegative.
Qed.

(** Source for [zero_endpoint_degree_zero_time_moment]: the
    original degree-zero time coefficient is one at
    both zero endpoints, checking the middle equality
    of Federer 4.1.9, p. 364. *)
Example zero_endpoint_degree_zero_time_moment:
  is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
    (real_total_integrand (fun _=>1)) (1:R)%:E.
Proof.
have hMoment:=@scalar_affine_power_moment R 0 0 0%N.
change (is_measure_subset_integral (@lebesgue_scalar_measure R) (`[0,1]:set (real_line_metric R))
  (real_total_integrand (fun _=>1)) ((\sum_(k<1) (0:R)^+k*0^+(0-k))/1)%:E) in hMoment.
by rewrite big_ord1 !expr0 mulr1 divr1 in hMoment.
Qed.
End HomotopyCurrentEndpointExamples.
