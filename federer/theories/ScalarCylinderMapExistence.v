(** Federer (1969), 3.2.33, p. 270: prove the coordinate
    specification of the actual cylinder map has a unique solution. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps ScalarCylinderMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [scalar_cylinder_map_exists]: existence of the
    displayed map f, Federer 3.2.33, p. 270. The block
    construction proves the independent laws and is confined
    inside this opaque existence proof. No selected global map
    or new project axiom is introduced. *)
Theorem scalar_cylinder_map_exists (R:realType) mu k (g:R->R):
  exists F:R_n R ((mu+1)+k)->R_n R (mu+1),is_scalar_cylinder_map g F.
Proof.
pose F (x:R_n R ((mu+1)+k)):R_n R (mu+1):=
  euclidean_block_join
    ([ffun i=>x (lshift k (lshift 1 i))],
     euclidean_one_embed (g (x (lshift k (rshift mu ord0))))).
exists F; constructor.
- by move=>x i; rewrite /F euclidean_block_join_left ffunE.
- by move=>x; rewrite /F euclidean_block_join_right /euclidean_one_embed ffunE.
Qed.

(** Source for [scalar_cylinder_map_unique]: the explicit
    coordinate formula determines f uniquely, supporting all
    fibre identifications in Federer 3.2.33, p. 270. *)
Lemma scalar_cylinder_map_unique (R:realType) mu k (g:R->R)
    (F G:R_n R ((mu+1)+k)->R_n R (mu+1)):
  is_scalar_cylinder_map g F ->is_scalar_cylinder_map g G ->F=G.
Proof.
move=>hF hG; apply:funext=>x; apply/ffunP=>i.
rewrite -(splitK i); case:(split i)=>j.
- by rewrite (scalar_cylinder_first_coordinates hF) (scalar_cylinder_first_coordinates hG).
- rewrite (ord1 j); by rewrite (scalar_cylinder_last_coordinate hF) (scalar_cylinder_last_coordinate hG).
Qed.
