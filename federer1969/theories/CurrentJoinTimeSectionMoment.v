(** Federer (1969), 4.1.11, p. 365: integrate the
    exact original time section at every pair where the
    two spatial orientations are defined. Its value is
    the printed factorial coefficient times their spatial
    wedge mass, by the already proved absolute time moment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate ExteriorGrading CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed
  CurrentJoinDomain CurrentJoinRawCoordinates CurrentJoinTripleCoordinates CurrentJoinOriginalWeight
  CurrentJoinSpatialWeight CurrentJoinTimeRepresentation CurrentJoinTimeAbsoluteMoment
  ScalarUnitMixedPower ScalarBetaCoefficient DistributionIntegrationRepresentationUP
  NormalisedDistributionRepresentationUP PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinTimeSectionMoment.
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
Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation OS := (@CurrentOrientation.value R h2 n i Full hFull S hS).
Local Notation OT := (@CurrentOrientation.value R h2 n j Full hFull T hT).
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation hSegment := (@current_join_time_representable R h2).
Local Notation rho := (@NormalisedCurrent.measure R h2 1%N 1%N Time hTime Segment hSegment).
Local Notation hRho := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 1%N 1%N Time hTime Segment hSegment))).
Local Notation W := (@current_join_original_weight R h2 n i j S T hS hT).
Local Notation N := (@current_vector_mass R h2 n (i+(1+j))%N).
Local Notation J := (@current_join_triple_point R n).
Local Notation q := (fun t:TT=>@euclidean_one_project R (set_val t)).
Local Notation B := (@scalar_beta_coefficient R i j).

(** Source for [current_join_time_section_moment]: every
    original spatial orientation pair has the exact time
    integral B(i,j) times the printed spatial wedge mass,
    supporting equality of the two mass displays in
    Federer 4.1.11, p. 365. No spatial measurability or
    finite total mass is assumed in this pointwise assertion. *)
Theorem current_join_time_section_moment (x y:XT)
    (a:exterior_power X i) (b:exterior_power X j):
  partial_function_graph OS x a->partial_function_graph OT y b->
  is_measure_integral rho (partial_function_precompose (fun t:TT=>J (x,(t,y))) W)
    (B*N (@current_join_spatial_coefficient R n i j (x,y) a b))%:E.
Proof.
move=>hA hB.
pose c:=N (@current_join_spatial_coefficient R n i j (x,y) a b).
have hMoment:=@current_join_time_absolute_beta_moment R h2 hSegment i j.
have hScaled:=@real_total_integral_scale R TT rho hRho
  (fun t:TT=>`|@scalar_unit_mixed_power R i j (q t)|) B c hMoment.
have hValue:c*B=B*c:=mulrC _ _.
rewrite hValue in hScaled.
apply:(@measure_integral_graph_equivalent R TT rho _ _ _ _ hScaled)=>t v.
have hCoordinates:=@current_join_triple_point_coordinates R n (x,(t,y)).
have hPointGraph:partial_function_graph W (J (x,(t,y)))
    (c*`|@scalar_unit_mixed_power R i j (q t)|)%:E.
  apply:(@current_join_original_weight_graph R h2 n i j S T hS hT (J (x,(t,y))) _).2.
  exists a,b;split;first by rewrite hCoordinates.1.
  split;first by rewrite hCoordinates.2.2.
  rewrite (@current_join_original_vector_mass R h2 n i j (J (x,(t,y))) a b)
    (@current_join_spatial_coefficient_agreement R n i j x y t a b)
    /current_join_time_coordinate hCoordinates.2.1.
  by rewrite mulrC.
rewrite real_total_integrand_graph.
change ((c*`|@scalar_unit_mixed_power R i j (q t)|)%:E=v<->
  partial_function_graph W (J (x,(t,y))) v).
split.
- by move=>hEq;rewrite -hEq.
- move=>hGraph;exact:(partial_function_single_valued hPointGraph hGraph).
Qed.
End CurrentJoinTimeSectionMoment.
