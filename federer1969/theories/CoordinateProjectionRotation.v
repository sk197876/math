(** Federer (1969), 3.4.8(13), p. 336:
    choose psi_lambda with p_m=p_lambda psi_lambda.
    The existing transitivity theorem for actual orthogonal
    projections supplies the required frame extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology subtype_topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerMetric HomInner LinearBasis
  ExteriorIndices CoordinateProjection OrthogonalMaps OrthogonalInjectionSpaces OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  AnalyticPrefixCoordinatesSealed AnalyticPrefixOrthogonalProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CoordinateRotation.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation C:=(@euclidean_inner_product R m).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation hC:=(@euclidean_inner_productP R m).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation c:=(@coordinate_basis R m).
Local Notation hc:=(@coordinate_basisP R m).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega m hMN).
Local Notation om:=(@orthogonal_element_map R X B hB n e he).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.

(** Source for [coordinate_projection_rotation]: the original
    equation p_m=p_lambda psi_lambda, 3.4.8(13),
    p. 336, including the zero-dimensional projections. *)
Theorem coordinate_projection_rotation (lambda:Lambda n m):
  exists psi:O,forall x,P x=@coordinate_projection R n m lambda (om psi x).
Proof.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
have hPrefix:=@analytic_prefix_projection_orthogonal R X B hB n e he
  (@euclidean_coordinate_orthonormal_family R n) omega hDual m hMN P
  (@AnalyticPrefixCoordinates.inclusion R X n e m hMN)
  (@AnalyticPrefixCoordinates.projection_laws R X n omega m hMN)
  (@AnalyticPrefixCoordinates.inclusion_laws R X n e m hMN).
have hCoordinate:=(O_star_projection _).1 (@coordinate_projection_orthogonal R n m lambda).
pose p1:=orthogonal_projection_of hC hB he hCoordinate.
pose p2:=orthogonal_projection_of hC hB he hPrefix.
have [g hG]:=@orthogonal_projection_action_transitive R Y X C B hC hB m c n e hc he
  mulO invO unitO hO p1 p2.
exists (invO g)=>x.
have hEqual:=congr1 (fun q=>orthogonal_projection_map q x) hG.
rewrite orthogonal_projection_actionE in hEqual.
exact:esym hEqual.
Qed.
End CoordinateRotation.
