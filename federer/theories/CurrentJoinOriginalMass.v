(** Federer (1969), 4.1.11, p. 365: the original
    sharp join mass bound with both literal partial
    orienting fields. The preceding exact source-density
    identity transfers the actual proper-image integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion NormalisedCurrentSealed CurrentMassSealed
  CurrentJoinDomain CurrentJoinMapSealed CurrentJoinSealed CurrentJoinRawCoordinates
  CurrentJoinRawRepresentation CurrentJoinRawMass CurrentJoinOriginalWeight CurrentJoinRawDensityAgreement
  CurrentImageDensityPairing DistributionIntegrationRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinOriginalMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation Domain := (@current_join_domain R n).
Local Notation CT := (current_domain R (n+(1+n))%N Domain).
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation lambda := (@current_join_raw_measure R h2 n i j S T hS hT).
Local Notation zeta := (@current_join_raw_density R h2 n i j S T hS hT).
Local Notation hLambda := (distribution_representation_measure
  (@current_join_raw_representation R h2 n i j S T hS hT)).
Local Notation N := (@current_vector_mass R h2 n (i+(1+j))%N).
Local Notation W := (@current_join_original_weight R h2 n i j S T hS hT).
Local Notation Auxiliary := (real_total_integrand (fun z:CT=>N
  (@current_image_density R (n+(1+n))%N n (i+(1+j))%N Domain (@CurrentJoinMap.value R n) zeta z))).

(** Source for [current_join_original_weight_agreement]: the
    actual exterior-image mass agrees almost everywhere
    with the original partial wedge weight, supporting
    Federer 4.1.11, p. 365, first mass display. *)
Theorem current_join_original_weight_agreement:
  measure_almost_equal lambda Auxiliary W.
Proof.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _
  (measure_almost_everywhere_and hLambda
    (@current_join_raw_factor_orientations R h2 n i j S T hS hT)
    (@current_join_raw_exterior_image R h2 n i j S T hS hT)))=>z [[hA hB] hImage].
pose a:=@NormalisedCurrent.auxiliary_density R h2 n i Full hFull S hS
  (@current_join_first_point R n z).
pose b:=@NormalisedCurrent.auxiliary_density R h2 n j Full hFull T hT
  (@current_join_last_point R n z).
exists (N (@current_join_original_vector R n i j z a b))%:E;split.
- by rewrite real_total_integrand_graph hImage.
- apply:(@current_join_original_weight_graph R h2 n i j S T hS hT z _).2.
  exists a,b;split;first exact:hA.
  split;[exact:hB|by []].
Qed.

(** Source for [current_join_original_weight_integral]: the
    literal original partial weight has its nonnegative
    integral on the original product variation, supporting
    Federer 4.1.11, p. 365. Infinite integral values remain allowed. *)
Theorem current_join_original_weight_integral:
  is_measure_integral lambda W (measure_lower_integral lambda W).
Proof.
have hAux:=@current_join_raw_mass_integral R h2 n i j S T hS hT.
have hOriginal:=@measure_integral_almost_equal R CT lambda hLambda Auxiliary W _
  hAux current_join_original_weight_agreement.
have hValue:=@measure_lower_integral_unique R CT lambda W
  (measure_lower_integral lambda W) (measure_lower_integral lambda Auxiliary)
  (measure_lower_integral_specification lambda W) hOriginal.2.2.
by rewrite -hValue in hOriginal.
Qed.

(** Source for [current_join_original_weight_measurable]:
    the exact printed partial weight is measurable,
    supporting Federer 4.1.11, p. 365. The original
    partial domains are preserved. *)
Theorem current_join_original_weight_measurable:is_measure_measurable_function lambda W.
Proof. exact:current_join_original_weight_integral.1. Qed.

(** Source for [current_join_original_weight_nonnegative]:
    the literal mass weight is nonnegative on its
    conull original domain, supporting the nonnegative
    Fubini calculation in Federer 4.1.11, p. 365. *)
Theorem current_join_original_weight_nonnegative:
  measure_almost_everywhere lambda (partial_extended_nonnegative_locus W).
Proof.
have hDomain:=measurable_function_domain current_join_original_weight_measurable.
apply:(@measure_almost_everywhere_mono R CT lambda hLambda _ _ _ hDomain)=>z [v hGraph].
have [a [b [_ [_ hValue]]]]:=(@current_join_original_weight_graph R h2 n i j S T hS hT z v).1 hGraph.
exists v;split;first exact:hGraph.
rewrite -hValue lee_fin;exact:real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n (i+(1+j))%N).1 _.
Qed.

(** Source for [current_join_original_mass_bound]: the mass
    of the actual original join is at most the integral
    of its exact printed partial wedge weight, Federer
    4.1.11, p. 365. Only the original compact supports
    and integration representations are required. *)
Theorem current_join_original_mass_bound
    (hSC:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n Full hFull i S))
    (hTC:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n Full hFull j T)):
  (@CurrentMass.value R h2 n (i+1+j)%N Full hFull (@CurrentJoin.value R h2 n i j S T hSC hTC)<=
    measure_lower_integral lambda W)%E.
Proof.
have hAux:=@measure_integral_almost_equal R CT lambda hLambda W Auxiliary _
  current_join_original_weight_integral (measure_almost_equal_sym current_join_original_weight_agreement).
exact:(@current_join_raw_mass_bound R h2 n i j S T hSC hTC hS hT _ hAux).
Qed.
End CurrentJoinOriginalMass.
