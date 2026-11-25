(** Federer (1969), 3.3.4, pp. 290–292:
    actual projective Hausdorff null sets
    pull back to actual normalized Haar
    null sets. The finite positive total
    mass is proved, not supplied as a
    missing hypothesis of the numbered lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct StructureProjectiveSpace StructureProjectiveMeasure
  StructureProjectiveHaarMeasure EuclideanOrthogonalInvariantMeasures
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed
  CompactGroupHaarNormalisation HomogeneousSpaceUP MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_haar_orbit_null]:
    the passage from H^m nullity to
    beta[F inverse bad]=0 in Federer
    3.3.4, pp. 290–292. The exact
    actual Haar-orbit identity and positive
    projective total mass permit cancellation;
    arbitrary original null subsets are retained. *)
Theorem structure_projective_haar_orbit_null (R:realType) m
    (mulS:euclidean_orthogonal_group R m.+1->euclidean_orthogonal_group R m.+1->euclidean_orthogonal_group R m.+1)
    (invS:euclidean_orthogonal_group R m.+1->euclidean_orthogonal_group R m.+1)
    (eS:euclidean_orthogonal_group R m.+1)
    (hS:is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1))
      (linear_group_inv (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1))
      (linear_group_unit (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1))
      (euclidean_orthogonal_group R m.+1) mulS invS eS)
    (theta:set (set_type (euclidean_orthogonal_group R m.+1))->\bar R)
    (x:structure_projective_space R m) (B:set (structure_projective_space R m)):
  @is_normalised_haar_measure R
    [the topologicalType of set_type (euclidean_orthogonal_group R m.+1)] mulS theta ->
  @structure_projective_measure R m B=0%E ->
  theta ((orbit_map (@structure_projective_action R m) x) @^-1` B)=0%E.
Proof.
move=>hTheta hNull.
have hMass:=@structure_projective_haar_measure R m mulS invS eS hS theta x hTheta B.
have hPositive:(0<@structure_projective_measure R m setT)%E:=
  (andP (@structure_projective_measure_positive_finite R m)).1.
have hNonzero:structure_projective_measure (@setT (structure_projective_space R m))!=0%E.
  by rewrite (gt_eqF hPositive).
rewrite hNull /measure_pushforward in hMass.
apply/eqP; move/eqP:(esym hMass).
by rewrite mule_eq0 (negbTE hNonzero) /=.
Qed.
