(** Federer (1969), 4.1.11, p. 365: the exact
    factorial mass coefficient and both original repeated
    integrals. Integrate time first through the preceding
    product-measure regrouping, then use the original
    positive-scaling law of 2.4.4(3), pp. 82–83. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentMassSealed CurrentJoinDomain CurrentJoinSealed CurrentJoinOriginalWeight
  CurrentJoinOriginalMass CurrentJoinRawRepresentation CurrentJoinTripleCoordinates CurrentJoinTripleMeasure
  CurrentJoinSpatialWeight CurrentJoinTimeRepresentation CurrentJoinTimeFirstMeasure CurrentJoinTimeSectionMoment
  ScalarBetaCoefficient DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialProductSections
  ParameterizedIntegral MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  ProductMeasure CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  MeasureIntegralGraphEquivalence MeasureUpperIntegralScale MeasureIntegralScaleLaw ProductFunctionFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinMassCoefficient.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hTime := (fun (t:R_n R 1%N) (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
  (inner_norm (@euclidean_inner_productP R 1%N)) t).
Local Notation XT := (current_domain R n Full).
Local Notation TT := (current_domain R 1%N Time).
Local Notation PT := (Choice.clone (XT*XT)%type _).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_representable R h2).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n i Full hFull S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j Full hFull T hT).
Local Notation rho := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n i Full hFull S hS).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j Full hFull T hT).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n i Full hFull S hS))).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n j Full hFull T hT))).
Local Notation delta := (product_measure hAlpha hBeta).
Local Notation hDelta := (product_measure_is_measure hAlpha hBeta).
Local Notation lambda := (@current_join_raw_measure R h2 n i j S T hS hT).
Local Notation W := (@current_join_original_weight R h2 n i j S T hS hT).
Local Notation G := (@current_join_spatial_weight R h2 n i j S T hS hT).
Local Notation J := (@current_join_triple_point R n).
Local Notation N := (@current_vector_mass R h2 n (i+(1+j))%N).
Local Notation B := (@scalar_beta_coefficient R i j).
Local Notation I := (measure_lower_integral lambda W).
Local Notation Spatial := (measure_lower_integral delta G).
Local Notation TimeIntegral := (parameterized_integral rho (fun xy:XT*XT=>
  partial_function_precompose (fun t:TT=>J (xy.1,(t,xy.2))) W)).

(** Source for [current_join_time_integral_spatial_agreement]:
    the actual original inner time integrals agree almost
    everywhere with the printed factorial coefficient times
    the original partial spatial weight, Federer 4.1.11,
    p. 365, equality of the two mass displays. *)
Theorem current_join_time_integral_spatial_agreement:
  measure_almost_equal delta TimeIntegral (partial_extended_function_scale B G).
Proof.
apply:(@measure_almost_everywhere_mono R PT delta hDelta _ _ _
  (@current_join_spatial_factor_orientations R h2 n i j S T hS hT))=>xy [hA hB].
pose a:=xi xy.1.
pose b:=eta xy.2.
pose c:=N (@current_join_spatial_coefficient R n i j xy a b).
exists (B*c)%:E;split.
- apply:(parameterized_integral_specification rho _ xy _).2.
  exact:(@current_join_time_section_moment R h2 n i j S T hS hT xy.1 xy.2 a b hA hB).
- exists c%:E;split.
  + apply:(@current_join_spatial_weight_graph R h2 n i j S T hS hT xy _).2.
    exists a,b;split;first exact:hA.
    split;[exact:hB|by []].
  + by rewrite -EFinM.
Qed.

(** Source for [current_join_scaled_spatial_integral]: the
    scaled original partial spatial weight has exactly the
    original triple integral, supporting Federer 4.1.11,
    p. 365. Its integrability is proved by Fubini. *)
Theorem current_join_scaled_spatial_integral:
  is_measure_integral delta (partial_extended_function_scale B G) I.
Proof.
have hTime:=@current_join_time_first_fubini R h2 n i j S T hS hT W I
  (@current_join_original_weight_integral R h2 n i j S T hS hT).
exact:(measure_integral_almost_equal hDelta hTime current_join_time_integral_spatial_agreement).
Qed.

(** Source for [current_join_mass_coefficient_identity]: the
    original triple mass integral is exactly i!j!/(i+j+1)!
    times its original spatial mass integral, Federer
    4.1.11, p. 365. Infinite values and both zero degrees
    are retained under the printed positive coefficient. *)
Theorem current_join_mass_coefficient_identity:I=(B%:E*Spatial)%E.
Proof.
have hValue:=@measure_lower_integral_unique R PT delta (partial_extended_function_scale B G)
  (measure_lower_integral delta (partial_extended_function_scale B G)) I
  (measure_lower_integral_specification delta _) current_join_scaled_spatial_integral.2.2.
rewrite (@measure_lower_integral_positive_scale R PT delta hDelta B G
  (@scalar_beta_coefficient_positive R i j)) in hValue.
exact:esym hValue.
Qed.

(** Source for [current_join_spatial_weight_integral]: the
    literal original spatial weight is integrable with its
    actual lower integral, supporting the second displayed
    mass bound in Federer 4.1.11, p. 365. No separate
    measurability premise is added. *)
Theorem current_join_spatial_weight_integral:is_measure_integral delta G Spatial.
Proof.
have hB:B!=0 by rewrite gt_eqF //;exact:(@scalar_beta_coefficient_positive R i j).
have hInverse:B^-1!=0 by rewrite invr_eq0.
have hScaled:=@measure_integral_nonzero_scale R PT delta hDelta B^-1
  (partial_extended_function_scale B G) I hInverse current_join_scaled_spatial_integral.
have hIntegral:=@measure_integral_graph_equivalent R PT delta _ G _
  (@inverse_scale_graph R PT B G hB) hScaled.
have hValue:=@measure_lower_integral_unique R PT delta G Spatial _
  (measure_lower_integral_specification delta G) hIntegral.2.2.
by rewrite -hValue in hIntegral.
Qed.

(** Source for [current_join_spatial_double_integral]: the
    literal original x,y repeated integral exists and has
    exactly the spatial product-integral value, supporting
    the second mass display in Federer 4.1.11, p. 365. *)
Theorem current_join_spatial_double_integral:
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section G)) Spatial.
Proof.
have [hX [_ hY]]:=@current_join_factors_countably_measurable R h2 n i j S T hS hT.
have hWhole:=@product_whole_countably_measurable R XT XT alpha beta hAlpha hBeta hX hY.
have hCount:=@countably_measurable_function_on_countable_source R (XT*XT)%type
  (extended_real_line R) delta hDelta 0%E G (@extended_real_zero_closed R) hWhole current_join_spatial_weight_integral.1.
exact:(@product_function_fubini R XT XT alpha beta hAlpha hBeta G Spatial
  current_join_spatial_weight_integral hCount).1.
Qed.

(** Source for [current_join_original_triple_integral]: the
    literal original x,t,y repeated integral exists and
    has exactly the sharp mass-integral value, supporting
    the first mass display in Federer 4.1.11, p. 365. *)
Theorem current_join_original_triple_integral:
  is_measure_integral alpha (parameterized_integral rho (fun x:XT=>
    parameterized_integral beta (fun t:TT=>
      partial_function_precompose (fun y:XT=>J (x,(t,y))) W))) I.
Proof.
exact:(@current_join_triple_fubini R h2 n i j S T hS hT W I
  (@current_join_original_weight_integral R h2 n i j S T hS hT)).
Qed.

(** Source for [current_join_factorial_mass_bound]: the mass
    of the original join is bounded by i!j!/(i+j+1)!
    times the literal spatial wedge-mass integral,
    Federer 4.1.11, p. 365. Only the original compact
    supports and integration representations are required. *)
Theorem current_join_factorial_mass_bound
    (hSC:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n Full hFull i S))
    (hTC:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n Full hFull j T)):
  (@CurrentMass.value R h2 n (i+1+j)%N Full hFull (@CurrentJoin.value R h2 n i j S T hSC hTC)<=
    B%:E*Spatial)%E.
Proof.
rewrite -current_join_mass_coefficient_identity.
exact:(@current_join_original_mass_bound R h2 n i j S T hS hT hSC hTC).
Qed.
End CurrentJoinMassCoefficient.
