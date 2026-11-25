(** Federer (1969), 4.1.11, pp. 364–365: the join map
    sends (x,t,y) to (1-t)x+ty. Specify that formula before
    proving existence. The original Euclidean block identifications
    retain the order x, t, y, including zero-dimensional blocks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate
  EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentJoinMapUP.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation point := (fun (x : X) (t : R) (y : X) =>
  @euclidean_block_join R n (1+n)%N
    (x, @euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).

(** Source for [is_current_join_map]: the opening displayed formula
    F(x,t,y)=(1-t)x+ty, Federer 4.1.11, p. 364. This predicate
    adds no smoothness, properness, current or existence premise. *)
Definition is_current_join_map (F : Z -> X) : Prop :=
  forall (x : X) (t : R) (y : X),
    F (point x t y) = (1-t) *: x + t *: y.

(** Source for [current_join_map_exists]: existence of the original
    map F in Federer 4.1.11, p. 364. The coordinate construction
    serves only as a witness for the independent affine formula. *)
Theorem current_join_map_exists :
  exists F : Z -> X, is_current_join_map F.
Proof.
exists (fun z : Z =>
  let p := @euclidean_block_split R n (1+n)%N z in
  let q := @euclidean_block_split R 1%N n p.2 in
  let t := @euclidean_one_project R q.1 in
  (1-t) *: p.1 + t *: q.2).
move=> x t y.
rewrite euclidean_block_joinK.
change ((1- @euclidean_one_project R
    (@euclidean_block_split R 1%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).1)
    *: x + @euclidean_one_project R
      (@euclidean_block_split R 1%N n
        (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).1
    *: (@euclidean_block_split R 1%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).2
    = (1-t)*:x+t*:y).
by rewrite euclidean_block_joinK /= euclidean_one_embedK.
Qed.

(** Source for [current_join_map_unique]: the original formula
    determines F on every Euclidean point, supporting Federer
    4.1.11, p. 364. Both block inverses are the preceding ones. *)
Theorem current_join_map_unique (F G : Z -> X) :
  is_current_join_map F -> is_current_join_map G -> F = G.
Proof.
move=> hF hG; apply: funext => z.
pose p := @euclidean_block_split R n (1+n)%N z.
pose q := @euclidean_block_split R 1%N n p.2.
have hz : point p.1 (@euclidean_one_project R q.1) q.2 = z.
  by rewrite euclidean_one_projectK /q euclidean_block_splitK
    /p euclidean_block_splitK.
by rewrite -hz hF hG.
Qed.

(** Source for [current_join_map_start]: F(x,0,y)=x,
    used in the first paragraph of Federer 4.1.11, p. 365. *)
Lemma current_join_map_start (F : Z -> X)
    (hF : is_current_join_map F) (x y : X) : F (point x 0 y) = x.
Proof. by rewrite hF subr0 scale1r scale0r addr0. Qed.

(** Source for [current_join_map_end]: F(x,1,y)=y,
    used in the first paragraph of Federer 4.1.11, p. 365. *)
Lemma current_join_map_end (F : Z -> X)
    (hF : is_current_join_map F) (x y : X) : F (point x 1 y) = y.
Proof. by rewrite hF subrr scale0r scale1r add0r. Qed.
End CurrentJoinMapUP.
