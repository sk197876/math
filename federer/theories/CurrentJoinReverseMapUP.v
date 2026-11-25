(** Federer (1969), 4.1.11, p. 365: specify the
    original reversing map before proving its existence and
    sealing it. The coordinate order remains x, t, y. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate
  EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentJoinReverseMapUP.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation point := (fun (x : X) (t : R) (y : X) =>
  @euclidean_block_join R n (1+n)%N
    (x, @euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).

(** Source for [is_current_join_reverse_map]: the original
    p(x,t,y)=(y,1-t,x), Federer 4.1.11, p. 365, paragraph on
    anticommutativity. This independent predicate assumes only
    the printed coordinate values. *)
Definition is_current_join_reverse_map (p:Z->Z):Prop:=
  forall (x:X) (t:R) (y:X),p (point x t y)=point y (1-t) x.

(** Source for [current_join_reverse_map_exists]: existence
    of the original reversing map in Federer 4.1.11, p. 365.
    The coordinate construction serves only as a witness to
    the independent printed formula. *)
Theorem current_join_reverse_map_exists:
  exists p:Z->Z,is_current_join_reverse_map p.
Proof.
exists (fun z:Z=>
  let a:=@euclidean_block_split R n (1+n)%N z in
  let b:=@euclidean_block_split R 1%N n a.2 in
  point b.2 (1- @euclidean_one_project R b.1) a.1).
move=>x t y;rewrite euclidean_block_joinK.
change (point
    (@euclidean_block_split R 1%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).2
    (1- @euclidean_one_project R
      (@euclidean_block_split R 1%N n
        (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,y))).1) x=
  point y (1-t) x).
by rewrite euclidean_block_joinK /= euclidean_one_embedK.
Qed.

(** Source for [current_join_reverse_map_unique]: the original
    values determine p everywhere, supporting Federer 4.1.11,
    p. 365. Reuse both original block inverse laws. *)
Theorem current_join_reverse_map_unique (p q:Z->Z):
  is_current_join_reverse_map p->is_current_join_reverse_map q->p=q.
Proof.
move=>hp hq;apply:funext=>z.
pose a:=@euclidean_block_split R n (1+n)%N z.
pose b:=@euclidean_block_split R 1%N n a.2.
have hz:point a.1 (@euclidean_one_project R b.1) b.2=z.
  by rewrite euclidean_one_projectK /b euclidean_block_splitK
    /a euclidean_block_splitK.
by rewrite -hz hp hq.
Qed.
End CurrentJoinReverseMapUP.
