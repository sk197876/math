(** Federer (1969), 4.1.11, p. 365, opening paragraph:
    G_t(x,y)=(x,t,y). Specify the original insertion independently.
    The already defined product map and point inclusion supply
    only an existence witness; both blocks may be zero-dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanCartesianMap
  CurrentCartesianPointInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinSliceMapUP.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Source := (R_n R (n+n)%N).
Local Notation Target := (R_n R (n+(1+n))%N).
Variable t : R.

(** Source for [is_current_join_slice_map]: the original
    formula G_t(x,y)=(x,t,y), Federer 4.1.11, p. 365,
    opening paragraph. It assumes no existence or current identity. *)
Definition is_current_join_slice_map (G : Source -> Target) : Prop :=
  forall (x y : X), G (@euclidean_block_join R n n (x,y)) =
    @euclidean_block_join R n (1+n)%N
      (x,@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y)).

(** Source for [current_join_slice_map_exists]: existence of
    the original insertion G_t, supporting Federer 4.1.11,
    p. 365. Reuse the componentwise map and point inclusion. *)
Theorem current_join_slice_map_exists :
  exists G : Source -> Target, is_current_join_slice_map G.
Proof.
exists (@euclidean_cartesian_map R n n n (1+n)%N (fun x : X => x)
  (@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t))).
move=> x y.
by rewrite /euclidean_cartesian_map euclidean_block_joinK.
Qed.

(** Source for [current_join_slice_map_unique]: the original
    coordinate formula determines G_t, supporting Federer 4.1.11,
    p. 365. Reuse the original inverse block identification. *)
Theorem current_join_slice_map_unique (G H : Source -> Target) :
  is_current_join_slice_map G -> is_current_join_slice_map H -> G = H.
Proof.
move=> hG hH; apply: funext => z.
pose p := @euclidean_block_split R n n z.
have hz : @euclidean_block_join R n n (p.1,p.2)=z.
  exact: euclidean_block_splitK.
by rewrite -hz hG hH.
Qed.
End CurrentJoinSliceMapUP.
