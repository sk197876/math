(** Federer (1969), 4.1.10, p. 364: the affine homotopy from
    the constant map with value u to the identity. The formula specifies
    the map independently; existence uses the preceding Euclidean block
    identification. No time enlargement of a star-shaped open set is
    assumed. The map here has the whole ambient space as target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate
  EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentConeHomotopyUP.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).

(** Source for [is_current_cone_homotopy]: Federer 4.1.10,
    p. 364, opening sentence, using the affine formula immediately above.
    At time t the original point x is sent to (1-t)u+tx. *)
Definition is_current_cone_homotopy (u : X) (h : Z -> X) : Prop :=
  forall (t : R) (x : X),
    h (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)) =
      (1-t) *: u + t *: x.

(** Source for [current_cone_homotopy_exists]: existence of the
    original affine map, supporting Federer 4.1.10, p. 364. The
    construction is only a witness for the independent formula. *)
Theorem current_cone_homotopy_exists (u : X) :
  exists h : Z -> X, is_current_cone_homotopy u h.
Proof.
exists (fun z : Z =>
  let p := @euclidean_block_split R 1%N n z in
  let t := @euclidean_one_project R p.1 in (1-t) *: u + t *: p.2).
move=> t x.
by rewrite euclidean_block_joinK /= euclidean_one_embedK.
Qed.

(** Source for [current_cone_homotopy_unique]: the formula determines
    the original map, supporting Federer 4.1.10, p. 364. Reuse both
    inverse block identifications from 2.6.5, p. 120. *)
Theorem current_cone_homotopy_unique (u : X) (h k : Z -> X) :
  is_current_cone_homotopy u h -> is_current_cone_homotopy u k -> h = k.
Proof.
move=> hH hK; apply: funext => z.
pose p := @euclidean_block_split R 1%N n z.
have hz : @euclidean_block_join R 1%N n
    (@euclidean_one_embed R (@euclidean_one_project R p.1),p.2) = z.
  by rewrite euclidean_one_projectK /p euclidean_block_splitK.
by rewrite -hz hH hK.
Qed.

(** Source for [current_cone_homotopy_start]: the initial map is
    constant with value u, Federer 4.1.10, p. 364, opening sentence. *)
Theorem current_cone_homotopy_start (u : X) (h : Z -> X)
    (hH : is_current_cone_homotopy u h) (x : X) :
  h (@euclidean_block_join R 1%N n (@euclidean_one_embed R 0,x)) = u.
Proof. by rewrite hH subr0 scale1r scale0r addr0. Qed.

(** Source for [current_cone_homotopy_end]: the final map is the
    identity, Federer 4.1.10, p. 364, opening sentence. *)
Theorem current_cone_homotopy_end (u : X) (h : Z -> X)
    (hH : is_current_cone_homotopy u h) (x : X) :
  h (@euclidean_block_join R 1%N n (@euclidean_one_embed R 1,x)) = x.
Proof. by rewrite hH subrr scale0r scale1r add0r. Qed.
End CurrentConeHomotopyUP.
