(** Federer (1969), 3.3.4, pp. 288–292: the original three
    alternatives hold for almost every actual orthogonal frame. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanBlockLinearMaps EuclideanProjectionSpace OrthogonalInjectionSpaces OrthogonalMaps
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure IsotropyGroupTopology
  LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation
  StructureConeUP StructureCoordinateAlternatives StructurePlaneGrowth StructureProjectionKernel
  StructureCoordinateHaarNull StructureFrameProjection StructureFrameGrowthAlternatives
  MeasureUP MeasureAlmostUP MeasureAlmostBasic SuslinSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Frames.
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

(** Source for [structure_frame_almost_everywhere_trichotomy]: Federer
    3.3.4, pp. 288–292. The finite intersection of the proved original
    coordinate alternatives has full actual Haar measure. If original
    plane accumulation fails, either some C_j supplies infinite growth
    or every B_j supplies ordinary zero growth. Every geometric and
    measure-theoretic premise comes from the preceding actual theorems. *)
Theorem structure_frame_almost_everywhere_trichotomy:
  (0<k)%N ->is_structure_measure phi ->is_suslin_set R A ->
  is_normalised_haar_measure mulS theta ->
  measure_almost_everywhere theta [set g:N|structure_plane_trichotomy m phi A a
    (structure_projection_kernel hmn (AP g p0))].
Proof.
move=>hk hPhi hA hTheta.
have hMeasure:is_measure theta.
  have [J [hNJ hM hRep hRegular]]:=hTheta.1; exact:hM.
pose Good (j:'I_k):set N:=
  [set g|((structure_coordinate_zero_growth phi A a
      (hom_as_linear (orthogonal_element_map (invS g))) j \/
    structure_coordinate_infinite_growth phi A a
      (hom_as_linear (orthogonal_element_map (invS g))) j) \/
    structure_plane_accumulation A a (structure_projection_kernel hmn (AP g p0)))].
have hEach j:measure_almost_everywhere theta (Good j).
  exact:(@structure_coordinate_haar_exception_null R m k hmn mulS invS eS hS
    theta p0 hP0 phi A a j hPhi hA hTheta).
have hCount:countable (@setT 'I_k):=finite_set_countable (@finite_finset [the finType of 'I_k] setT).
have hAll:=@measure_almost_everywhere_countable R [the choiceType of set_type O]
  [the choiceType of 'I_k] theta hMeasure setT Good hCount (fun j _=>hEach j).
apply:(measure_almost_everywhere_mono hMeasure _ hAll)=>g hGood.
case:(pselect (structure_plane_accumulation A a (structure_projection_kernel hmn (AP g p0))))=>hAccum.
  by right; right.
case:(pselect (exists j:'I_k,structure_coordinate_infinite_growth phi A a
    (hom_as_linear (orthogonal_element_map (invS g))) j))=>hInfinite.
- have [j hj]:=hInfinite; right; left.
  exact:(@structure_frame_infinite_growth R m k hmn phi A a
    (hom_as_linear (orthogonal_element_map (invS g))) (AP g p0) hPhi.1
    (orthogonal_element_orthogonal (invS g))
    (@structure_frame_projection_coordinates R m k mulS invS eS hS p0 hP0 g) hk j hj).
- left; apply:(@structure_frame_zero_growth R m k hmn phi A a
    (hom_as_linear (orthogonal_element_map (invS g))) (AP g p0) hPhi.1
    (orthogonal_element_orthogonal (invS g))
    (@structure_frame_projection_coordinates R m k mulS invS eS hS p0 hP0 g) hk)=>j.
  have hG:=hGood j I.
  case:hG=>[[hZero|hInf]|hAcc]; first exact:hZero.
  + exfalso; apply:hInfinite; by exists j.
  + exact:False_ind _ (hAccum hAcc).
Qed.
End Frames.
