(** Federer (1969), 3.2.13, p. 251: the normalized
    Haar orbit moment of |q(g C)| is beta_t(m,1)^t,
    from the actual projection constant of 2.7.16(6), p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions constructive_ereal
  topology subtype_topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  Hom ExteriorNorm ExteriorDiameterUP ExteriorPowers ExteriorDegreeOneNorm AssociatedSubspace
  OrthogonalProjectionConstants ProjectionBeta ProjectionConstantNorms RealPower
  OrthogonalInjectionSpaces OrthogonalGroupTopology OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws
  CompactGroupHomogeneousMeasures CompactGroupHaarNormalisation CompactHaarInverseIntegral
  UnitSphereSpace UnitSphereOrthogonalAction UnitSphereCoordinatePower FirstCoordinateProjection ProjectionDegreeOneOrbitNorm
  CompactSupportFunctionUP DaniellSpacePushforward PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence PushforwardIntegral
  RealIntegralFunctionalUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HaarMoment.
Variable R:realType.
Variable m:nat.
Variable hm:(0<m)%N.
Local Notation V:=(R_n R m).
Local Notation hB:=(@euclidean_inner_productP R m).
Local Notation hb:=(@coordinate_basisP R m).
Local Notation O:=(set_type (euclidean_orthogonal_group R m)).
Local Notation OP:=(set_type (euclidean_orthogonal_projections R m 1)).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (euclidean_orthogonal_group R m) mulS invS eS.

(** Source for [projection_beta_one_haar_integral]: the last
    equality in the displayed Haar comparison in Federer 3.2.13,
    p. 251. The projection-space definition is transported to
    the sphere orbit using degree-one naturality and Haar inversion. *)
Theorem projection_beta_one_haar_integral (theta:set O->\bar R)
    (x:euclidean_unit_sphere_space R m) (t:R):
  1<=t ->is_normalised_haar_measure mulS theta ->
  is_measure_integral theta
    (real_total_integrand (fun g=>unit_sphere_coordinate_power (Ordinal hm) t (unit_sphere_action g x)))
    (real_power (@projection_beta R m 1 hm t%:E) t)%:E.
Proof.
move=>ht hTheta.
pose h2:=real_exterior_two_nonzero R.
pose hG:=orthogonal_group_lch hS.
pose hGc:=@orthogonal_group_compact_space R V (@euclidean_inner_product R m) hB m
  (@coordinate_basis R m) hb.
pose q0:=@first_coordinate_projection_point R m hm.
pose Ap:=orthogonal_projection_action (@euclidean_inner_productP R 1) hB hb hS.
have hAp:=orthogonal_projections_homogeneous (@euclidean_inner_productP R 1) (@coordinate_basisP R 1) hS.
have hPhaus:=@orthogonal_projections_hausdorff R (R_n R 1) V
  (@euclidean_inner_product R 1) (@euclidean_inner_product R m) (@euclidean_inner_productP R 1) hB m
  (@coordinate_basis R m) hb.
pose phi:=MeasurePushforward.measure_pushforward (orbit_map Ap q0) theta.
have hPhi:=compact_orbit_pushforward_invariant hG hGc hAp hPhaus q0 hTheta.
pose C:=set_val x.
pose xi:=exterior_first_inclusion V C.
have hSimple:simple xi.
  exists [tuple C]; exact:exterior_first_word.
have hNorm:exterior_norm h2 hB xi= 1.
  rewrite /xi exterior_first_norm; exact:(set_valP x).
have ht0:0<t:=lt_le_trans ltr01 ht.
have htE:(1<=t%:E)%E by rewrite lee_fin.
have hBeta:=@projection_beta_specification R m 1 hm t%:E htE.
have hPi:=@projection_constant_integral R h2 t m 1
  (@projection_beta R m 1 hm t%:E) mulS invS eS hS phi xi hBeta ht0 hPhi hSimple.
rewrite hNorm real_power_one_base mulr1 in hPi.
have [[L [hL hThetaM hThetaRep hThetaReg]] hTheta1]:=hTheta.
pose F:=fun p:OP=>real_power (projection_norm h2 xi p) t.
have hFK:=projection_norm_power_compact h2 hS hSimple ht0.
have hFG:=compactly_supported_compose (orbit_map_continuous hAp q0)
  (compact_homogeneous_orbit_proper hGc hAp (x:=q0) hPhaus) hFK.
have hMeas:is_measure_measurable_function theta
    (partial_function_precompose (orbit_map Ap q0) (real_total_integrand F)).
  exact:(hThetaRep _ hFG).1.
have hOrbitI:=(@measure_pushforward_integral_iff R O OP theta hThetaM
  (orbit_map Ap q0) (real_total_integrand F) hMeas
  (real_power (@projection_beta R m 1 hm t%:E) t)%:E).2 hPi.
pose U:=fun g:O=>unit_sphere_coordinate_power (Ordinal hm) t (unit_sphere_action g x).
have hInverse:is_measure_integral theta (real_total_integrand (U\o invS))
    (real_power (@projection_beta R m 1 hm t%:E) t)%:E.
  apply:(measure_integral_graph_equivalent _ hOrbitI)=>g z.
  change (partial_function_graph (real_total_integrand F) (Ap g q0) z <->
    partial_function_graph (real_total_integrand (U\o invS)) g z).
  rewrite !real_total_integrand_graph.
  change ((real_power (projection_norm h2 (exterior_first_inclusion V C) (Ap g q0)) t)%:E=z <->
    (real_power `|orthogonal_element_map (invS g) C (Ordinal hm)| t)%:E=z).
  by rewrite /Ap /q0 projection_degree_one_orbit_norm.
have hAs:=@unit_sphere_homogeneous R m mulS invS eS hS hm.
have hUK:=compactly_supported_compose (orbit_map_continuous hAs x)
  (compact_homogeneous_orbit_proper hGc hAs (x:=x) (@euclidean_unit_sphere_space_hausdorff R m))
  (unit_sphere_coordinate_power_compact (Ordinal hm) ht0).
exact:(compact_haar_inverse_integral hG hGc hTheta.1 hUK hInverse).
Qed.
End HaarMoment.
