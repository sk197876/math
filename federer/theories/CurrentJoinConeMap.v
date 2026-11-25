(** Federer (1969), 4.1.11, p. 365: F(u,t,y)=h(t,y)
    for the original affine contraction h of 4.1.10,
    p. 364. Use only the two independently specified
    opaque maps and the original point inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates CurrentCartesianPointInclusion CurrentJoinMapSealed CurrentConeHomotopySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [current_join_cone_map]: the original point
    insertion followed by F is exactly the previous
    contraction h at every time and spatial point,
    Federer 4.1.11, p. 365, sentence after the cone identity. *)
Theorem current_join_cone_map (R:realType) n (u:R_n R n) (z:R_n R (1+n)%N):
  @CurrentJoinMap.value R n (@current_cartesian_point_inclusion R n (1+n)%N u z)=
    @CurrentConeHomotopy.value R n u z.
Proof.
pose p:=@euclidean_block_split R 1%N n z.
have hz:@euclidean_block_join R 1%N n (@euclidean_one_embed R (@euclidean_one_project R p.1),p.2)=z.
  by rewrite euclidean_one_projectK /p euclidean_block_splitK.
by rewrite -hz /current_cartesian_point_inclusion CurrentJoinMap.laws CurrentConeHomotopy.laws.
Qed.
