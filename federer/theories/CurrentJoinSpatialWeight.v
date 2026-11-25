(** Federer (1969), 4.1.11, p. 365: the literal
    spatial weight in the second mass display. The
    original S and T orienting fields retain their
    domains. Product-conull laws supply the original
    integration domain without choosing new field values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ExtendedRealOrderTopology RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading ExteriorPowers ExteriorHomogeneousProducts CurrentDomain CurrentSpaces
  CurrentCoefficientNorms CurrentIntegrationCriterion NormalisedCurrentSealed CurrentOrientationSealed
  CurrentOrientationAlmost CurrentJoinOriginalWeight CurrentJoinTripleCoordinates CurrentJoinRawCoordinates
  DistributionIntegrationRepresentationUP NormalisedDistributionRepresentationUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPrecomposition
  PartialFunctionPostcomposition PartialExtendedOrderLoci SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CartesianMeasureAlmost ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinSpatialWeight.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation XT := (current_domain R n Full).
Local Notation Time := (fun _:R_n R 1%N=>True).
Local Notation TT := (current_domain R 1%N Time).
Local Notation PT := (Choice.clone (XT*XT)%type _).
Local Notation V := (exterior_power X (i+(1+j))%N).
Local Notation N := (@current_vector_mass R h2 n (i+(1+j))%N).

(** Source for [current_join_spatial_coefficient]: the
    original xi wedge (y-x) wedge eta on the two spatial
    factors, Federer 4.1.11, p. 365, second mass display. *)
Definition current_join_spatial_coefficient (z:XT*XT)
    (a:exterior_power X i) (b:exterior_power X j):V:=
  exterior_product a (exterior_product (exterior_first_inclusion X (set_val z.2-set_val z.1)) b).

(** Source for [current_join_spatial_coefficient_agreement]:
    the original spatial coefficient is independent of the
    chosen time point, supporting the factorial simplification
    in Federer 4.1.11, p. 365. *)
Lemma current_join_spatial_coefficient_agreement (x y:XT) (t:TT) a b:
  @current_join_spatial_vector R n i j (@current_join_triple_point R n (x,(t,y))) a b=
    current_join_spatial_coefficient (x,y) a b.
Proof.
have hCoordinates:=@current_join_triple_point_coordinates R n (x,(t,y)).
by rewrite /current_join_spatial_vector /current_join_spatial_coefficient hCoordinates.1 hCoordinates.2.2.
Qed.

Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation OS := (@CurrentOrientation.value R h2 n i Full hFull S hS).
Local Notation OT := (@CurrentOrientation.value R h2 n j Full hFull T hT).
Local Notation alpha := (@NormalisedCurrent.measure R h2 n i Full hFull S hS).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j Full hFull T hT).
Local Notation xi := (@NormalisedCurrent.auxiliary_density R h2 n i Full hFull S hS).
Local Notation eta := (@NormalisedCurrent.auxiliary_density R h2 n j Full hFull T hT).
Local Notation hAlpha := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n i Full hFull S hS))).
Local Notation hBeta := (distribution_representation_measure (normalised_distribution_representation_laws
  (@NormalisedCurrent.laws R h2 n j Full hFull T hT))).
Local Notation delta := (product_measure hAlpha hBeta).
Local Notation hDelta := (product_measure_is_measure hAlpha hBeta).

(** Source for [current_join_spatial_weight]: the literal
    partial mass weight under the spatial double integral,
    Federer 4.1.11, p. 365. Its definition supplies no
    orienting values outside the original two domains. *)
Definition current_join_spatial_weight:partial_function PT (extended_real_line R):=
  partial_function_postcompose
    (partial_function_pair (partial_function_total (fun z:PT=>z))
      (partial_function_pair (partial_function_precompose fst OS)
        (partial_function_precompose snd OT)))
    (fun zab:PT*(exterior_power X i*exterior_power X j)=>
      (N (current_join_spatial_coefficient zab.1 zab.2.1 zab.2.2))%:E).

(** Source for [current_join_spatial_weight_graph]: the
    original spatial weight has exactly its printed wedge
    mass wherever both original orientations are defined,
    supporting Federer 4.1.11, p. 365. *)
Lemma current_join_spatial_weight_graph z v:
  partial_function_graph current_join_spatial_weight z v<->
  exists a,exists b,partial_function_graph OS z.1 a /\partial_function_graph OT z.2 b /\
    (N (current_join_spatial_coefficient z a b))%:E=v.
Proof.
split.
- move=>[[u [a b]] [[hPoint [hA hB]] hValue]].
  have hzu:z=u:=hPoint;subst u.
  exists a,b;split;first exact:hA.
  split;[exact:hB|exact:hValue].
- move=>[a [b [hA [hB hValue]]]].
  exists (z,(a,b));split;first by split;[|split].
  exact:hValue.
Qed.

(** Source for [current_join_spatial_factor_orientations]:
    the original two orientations agree with their actual
    auxiliary fields almost everywhere for the original
    product variation, supporting Federer 4.1.11, p. 365. *)
Theorem current_join_spatial_factor_orientations:
  measure_almost_everywhere delta [set z:PT|
    partial_function_graph OS z.1 (xi z.1) /\partial_function_graph OT z.2 (eta z.2)].
Proof.
have hFirst:=@product_almost_everywhere_first_factor R XT XT alpha beta hAlpha hBeta _
  (@current_orientation_normalised_agreement R h2 n i Full hFull S hS).
have hLast:=@product_almost_everywhere_second_factor R XT XT alpha beta hAlpha hBeta _
  (@current_orientation_normalised_agreement R h2 n j Full hFull T hT).
exact:(measure_almost_everywhere_and hDelta hFirst hLast).
Qed.

(** Source for [current_join_spatial_weight_domain_conull]:
    the literal spatial weight has a conull original domain,
    supporting Federer 4.1.11, p. 365. *)
Theorem current_join_spatial_weight_domain_conull:
  measure_almost_everywhere delta (partial_function_domain current_join_spatial_weight).
Proof.
apply:(@measure_almost_everywhere_mono R PT delta hDelta _ _ _
  current_join_spatial_factor_orientations)=>z [hA hB].
exists (N (current_join_spatial_coefficient z (xi z.1) (eta z.2)))%:E.
apply:(@current_join_spatial_weight_graph z _).2.
exists (xi z.1),(eta z.2);split;first exact:hA.
split;[exact:hB|by []].
Qed.
End CurrentJoinSpatialWeight.
