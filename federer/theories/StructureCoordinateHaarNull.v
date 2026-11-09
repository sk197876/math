(** Federer (1969), 3.3.4, pp. 289–292: the original coordinate
    alternatives and affine-plane accumulation cover almost every frame. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockLinearMaps EuclideanProjectionSpace OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation
  StructureConeUP StructureCoordinateAlternatives StructureOrthogonalCoordinateTopology
  StructureActiveCoordinatesUP StructureActiveCoordinatesExistence StructureActiveCoordinatesOrthogonal
  EuclideanInjectionExtension EuclideanInjectionExtensionTopology StructureCoordinateCosetNull
  StructureOrthogonalCosetAveraging StructureFrameProjection StructureParameterAccumulation
  StructureProjectionKernel StructurePlaneGrowth StructureFibreAccumulation SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Haar.
Variable R:realType.
Variables m k:nat.
Hypothesis hmn:(m<=m+k)%N.
Local Notation n:=(m+k).
Local Notation O:=(euclidean_orthogonal_group R n).
Local Notation N:=[the topologicalType of set_type O].
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R n)).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n)) O mulS invS eS.
Variable theta:set N->\bar R.
Variable p0:euclidean_projection_space R n m.
Hypothesis hP0:forall x,euclidean_projection_linear p0 x=@euclidean_first_block R m k x.
Local Notation AP:=(orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS).
Variables (phi:set E->\bar R) (A:set E) (a:E).

(** Source for [structure_coordinate_haar_exception_null]: Federer
    3.3.4, pp. 289–292, theta[complement(B_j union C_j union D)]=0.
    The actual active inclusion, active group operations and normalized
    Haar measure are obtained locally from proved existence. Original
    B_j and C_j are Borel; the original accumulation locus is Suslin.
    The projective coset theorem supplies every section's nullity, and
    the actual orthogonal Haar/Fubini theorem gives the conclusion. *)
Theorem structure_coordinate_haar_exception_null (j:'I_k):
  is_structure_measure phi ->is_suslin_set R A ->is_normalised_haar_measure mulS theta ->
  theta (~` ([set g:N|structure_coordinate_zero_growth phi A a
      (hom_as_linear (orthogonal_element_map (invS g))) j] `|`
    [set g:N|structure_coordinate_infinite_growth phi A a
      (hom_as_linear (orthogonal_element_map (invS g))) j] `|`
    [set g:N|structure_plane_accumulation A a (structure_projection_kernel hmn (AP g p0))]))=0%E.
Proof.
move=>hPhi hA hTheta.
have [w hW]:=@structure_active_inclusion_exists R m k j.
pose hOrth:=structure_active_inclusion_orthogonal hW.
pose iota:=@euclidean_injection_orthogonal_extension R (1+m) n w hOrth.
have [mulD [invD [eD hD]]]:=@orthogonal_group_restriction_exists R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1).
have [beta hBeta]:=@orthogonal_normalised_haar_measure_exists R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1) mulD invD eD hD.
apply:(@structure_orthogonal_coset_null_average R n m.+1 mulS invS eS mulD invD eD hS hD
  theta beta iota _ _ _ hTheta hBeta).
- exact:euclidean_injection_orthogonal_extension_continuous.
- exact:(@structure_orthogonal_coordinate_B_borel R m k mulS invS eS hS a phi A j hPhi).
- exact:(@structure_orthogonal_coordinate_C_borel R m k mulS invS eS hS a phi A j hPhi).
- exact:(@structure_parameter_accumulation_suslin R n m hmn N (fun g:N=>AP g p0) A a
    (@structure_frame_projection_continuous R m k mulS invS eS hS p0) hA).
- move=>g.
  exact:(@structure_coordinate_coset_exception_null R m k j hmn w hW
    mulS invS eS mulD invD eD hS hD beta p0 hP0 phi A a g hPhi.1 hA hBeta).
Qed.
End Haar.
