(** Federer (1969), 3.3.4, pp. 288–289: the original first-m
    frame projection and its continuous parameter map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanBlockLinearMaps EuclideanProjectionSpace OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure IsotropyGroupTopology
  LinearGroupTopology LinearGroupSealed TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Frame.
Variable R:realType.
Variables m k:nat.
Local Notation n:=(m+k).
Local Notation O:=(euclidean_orthogonal_group R n).
Local Notation N:=[the topologicalType of set_type O].
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  O mulS invS eS.
Variable p0:euclidean_projection_space R n m.
Local Notation AP:=(orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS).

(** Source for [structure_frame_projection_continuous]: the original
    frame-to-projection map in Federer 3.3.4, pp. 288–289, is continuous
    by the actual O(n) action on O*(n,m), 2.7.16(6), p. 139. The
    initial projection and group operations remain local parameters. *)
Theorem structure_frame_projection_continuous:continuous (fun g:N=>AP g p0).
Proof.
have hPair:continuous (fun g:N=>(g,p0):N*euclidean_projection_space R n m).
  apply:topological_pair_continuous; last exact:cst_continuous.
  by move=>g; exact:cvg_id.
have hAction:continuous (fun z:N*euclidean_projection_space R n m=>AP z.1 z.2).
  exact:orthogonal_projection_action_continuous.
move=>g; exact:(continuous_comp (hPair g) (hAction (g,p0))).
Qed.

(** Source for [structure_frame_projection_coordinates]: the actual
    first m coordinates in the frame g are p0 composed with g inverse,
    Federer 3.3.4, pp. 288–289. The law of the actual original
    coordinate projection gives every coordinate of this action. *)
Theorem structure_frame_projection_coordinates:
  (forall x,euclidean_projection_linear p0 x=@euclidean_first_block R m k x) ->
  forall (g:N) x,euclidean_projection_linear (AP g p0) x=
    @euclidean_first_block R m k (orthogonal_element_map (invS g) x).
Proof.
move=>hP g x.
change (orthogonal_projection_map (AP g p0) x=
  @euclidean_first_block R m k (orthogonal_element_map (invS g) x)).
rewrite orthogonal_projection_actionE; exact:hP.
Qed.
End Frame.
