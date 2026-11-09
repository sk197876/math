(** Federer (1969), 3.3.4, pp. 290–292: nullity of the original
    coordinate exception on each actual active-subgroup coset. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanBlockLinearMaps EuclideanProjectionSpace OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure IsotropyGroupTopology
  LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation HomogeneousSpaceUP
  MeasureUP MeasureAlmostBasic MeasureDerivationContext SuslinSetUP
  EuclideanMetricCompleteness EuclideanMetricSeparability
  StructureActiveCoordinatesUP StructureActiveCoordinatesOrthogonal EuclideanInjectionExtension
  StructureCentredDirectionCoordinates StructureDirectionMapUP StructureProjectiveSpace
  StructureProjectiveMeasure StructureProjectiveHaarNull StructureProjectiveAxisOrbit
  StructureRadialProjectiveAssembly StructureRadialProjectiveAlternatives
  StructureOpenBallGrowth StructureRadialImageMeasure StructureCoordinateGrowth
  StructureCoordinateAlternatives StructureCoordinateRadialTransport StructureCosetConePreimage
  StructureCosetFibreAccumulation StructureProjectionKernel StructurePlaneGrowth
  StructureFrameProjection PositiveRightOrderLimit PositiveRadiusLimits PositiveRadiusLimitCongruence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Coset.
Variable R:realType.
Variables m k:nat.
Variable j:'I_k.
Hypothesis hmn:(m<=m+k)%N.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R (m+k))).
Local Notation ON:=(euclidean_orthogonal_group R (m+k)).
Local Notation OD:=(euclidean_orthogonal_group R m.+1).
Variable w:Hom (R_n R (1+m)) (R_n R (m+k)).
Hypothesis hW:is_structure_active_inclusion j w.
Local Notation hOrth:=(structure_active_inclusion_orthogonal hW).
Local Notation iota:=(@euclidean_injection_orthogonal_extension R (1+m) (m+k) w hOrth).
Variables (mulN:ON->ON->ON) (invN:ON->ON) (eN:ON).
Variables (mulD:OD->OD->OD) (invD:OD->OD) (eD:OD).
Hypothesis hN:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  (linear_group_inv (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  (linear_group_unit (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  ON mulN invN eN.
Hypothesis hD:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1))
  (linear_group_inv (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1))
  (linear_group_unit (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1))
  OD mulD invD eD.
Variable beta:set (set_type OD)->\bar R.
Variable p0:euclidean_projection_space R (m+k) m.
Hypothesis hP0:forall x,euclidean_projection_linear p0 x=@euclidean_first_block R m k x.
Local Notation AP:=(orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)) hN).
Variables (phi:set E->\bar R) (A:set E) (a:E).

(** Source for [structure_coordinate_coset_exception_null]: Federer
    3.3.4, pp. 290–292: beta of the complement of B_j, C_j and D
    on every actual coset is zero. All projective derivation premises,
    Borel direction-map and nonzero-domain properties, literal cone
    cost identities and original fibre inclusions are proved for the
    actual original objects. No coset-nullity or numerator-regularity
    hypothesis is supplied. All auxiliary maps and directions are local. *)
Theorem structure_coordinate_coset_exception_null (g:ON):
  is_measure phi ->is_suslin_set R A ->is_normalised_haar_measure mulD beta ->
  beta [set h:set_type OD|~((
    structure_coordinate_zero_growth phi A a
      (hom_as_linear (orthogonal_element_map (invN (mulN g (iota h))))) j \/
    structure_coordinate_infinite_growth phi A a
      (hom_as_linear (orthogonal_element_map (invN (mulN g (iota h))))) j) \/
    structure_plane_accumulation A a (structure_projection_kernel hmn (AP (mulN g (iota h)) p0)))]=0%E.
Proof.
move=>hPhi hA hBeta.
pose L:=hom_comp (euclidean_rectangular_adjoint w) (orthogonal_element_map (invN g)).
pose q:=fun x:E=>(L (x-a):inner_metric_space (@euclidean_inner_productP R m.+1)).
pose D:set E:=[set x|0<inner_norm (@euclidean_inner_productP R m.+1) (q x)].
have [f [hF [hDomain hPuncture]]]:=@structure_centred_direction_map_exists R (m+k) m L a.
have [z0 [hAxis hOrbit]]:=@structure_projective_axis_orbit_exists R m.
pose F:=fun h:set_type OD=>structure_projective_action h z0.
pose P:=\bigcup_v @structure_radial_projective_zero R E m phi A D a f v.
pose Q:=\bigcap_v @structure_radial_projective_infinite R E m phi A D a f v.
pose S:=\bigcap_v @structure_radial_projective_image R E m A D a f v.
have hNull:structure_projective_measure (setT `\` (P `|` Q `|` S))=0%E.
  exact:(@structure_radial_projective_assembled_alternatives R E m phi A D a f
    hPhi (@euclidean_metric_complete R (m+k)) (@euclidean_metric_separable R (m+k)) hA hDomain hF.1).
have hOrbitNull:=@structure_projective_haar_orbit_null R m mulD invD eD hD beta z0
  (setT `\` (P `|` Q `|` S)) hBeta hNull.
have hBetaMeasure:is_measure beta.
  have [J [hNJ hMeasure hRep hRegular]]:=hBeta.1; exact:hMeasure.
apply:(measure_null_subset hBetaMeasure _ hOrbitNull)=>h hBad.
change (~((
    structure_coordinate_zero_growth phi A a
      (hom_as_linear (orthogonal_element_map (invN (mulN g (iota h))))) j \/
    structure_coordinate_infinite_growth phi A a
      (hom_as_linear (orthogonal_element_map (invN (mulN g (iota h))))) j) \/
    structure_plane_accumulation A a (structure_projection_kernel hmn (AP (mulN g (iota h)) p0)))) in hBad.
change ((setT `\` (P `|` Q `|` S)) (F h)).
split=>// hGood; apply:hBad.
have hGrowth delta t:0<t ->
    structure_open_ball_growth m (structure_radial_image_measure m phi A a D f delta) (F h) t=
    structure_coordinate_radial_supremum phi A a
      (hom_as_linear (orthogonal_element_map (invN (mulN g (iota h))))) j delta t.
  move=>ht; apply:structure_coordinate_radial_ball_transport=>// r s hs.
  exact:(@structure_coset_coordinate_cone_preimage R m k j w hW mulN invN eN hN
    A a g f hF h (F h) r s (hOrbit h) hs).
case:hGood=>[[hZero|hInfinite]|hImages].
- left; left; have [v _ hLimit]:=hZero.
  exists ((v.+1)%:R:R)^-1; split; first by rewrite invr_gt0 ltr0n.
  apply:(positive_right_extended_order_limit_congr (hGrowth ((v.+1)%:R:R)^-1)).
  exact:hLimit.
- left; right; apply:(structure_coordinate_infinite_reciprocal_iff phi A a
    (hom_as_linear (orthogonal_element_map (invN (mulN g (iota h))))) j).2=>v.
  have hLimit:=hInfinite v I.
  have hEq:=(positive_radius_limits_congr (hGrowth ((v.+1)%:R:R)^-1)).1.
  by rewrite -hEq; exact:hLimit.
- right.
  apply:(@structure_coset_original_image_accumulation R m k j w hW mulN invN eN hN
    A a g f hF hmn h (F h) (AP (mulN g (iota h)) p0) (hOrbit h) _ hImages).
  exact:(@structure_frame_projection_coordinates R m k mulN invN eN hN p0 hP0 (mulN g (iota h))).
Qed.
End Coset.
