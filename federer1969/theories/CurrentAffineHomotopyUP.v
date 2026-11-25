(** Federer (1969), 4.1.13, pp. 369–370: the affine
    homotopy joining the two original smooth maps. Its
    formula specifies the map independently; the coordinate
    construction is used only to prove existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate
  EuclideanBlockCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentAffineHomotopyUP.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).

(** Source for [is_current_affine_homotopy]: the original
    affine path (1-t)f(x)+tg(x) in Federer 4.1.13,
    p. 369. The formula is independent of open-domain,
    smoothness and support assertions. *)
Definition is_current_affine_homotopy (f g:X->Y) (h:Z->Y):Prop:=
  forall (t:R) (x:X),
    h (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))=
      (1-t)*:f x+t*:g x.

(** Source for [current_affine_homotopy_exists]: the affine
    homotopy used by Federer 4.1.13, pp. 369–370,
    exists in the original block coordinates of 2.6.5,
    p. 120. The explicit formula is only an existence witness. *)
Theorem current_affine_homotopy_exists (f g:X->Y):
  exists h:Z->Y,is_current_affine_homotopy f g h.
Proof.
exists (fun z:Z=>
  let p:=@euclidean_block_split R 1%N n z in
  let t:=@euclidean_one_project R p.1 in (1-t)*:f p.2+t*:g p.2).
move=>t x.
by rewrite euclidean_block_joinK /= euclidean_one_embedK.
Qed.

(** Source for [current_affine_homotopy_unique]: the original
    affine formula determines every value, supporting Federer
    4.1.13, pp. 369–370, by the block inverse laws
    of 2.6.5, p. 120. *)
Theorem current_affine_homotopy_unique (f g:X->Y) (h k:Z->Y):
  is_current_affine_homotopy f g h->is_current_affine_homotopy f g k->h=k.
Proof.
move=>hH hK;apply:funext=>z.
pose p:=@euclidean_block_split R 1%N n z.
have hz:@euclidean_block_join R 1%N n
    (@euclidean_one_embed R (@euclidean_one_project R p.1),p.2)=z.
  by rewrite euclidean_one_projectK /p euclidean_block_splitK.
by rewrite -hz hH hK.
Qed.

(** Source for [current_affine_homotopy_start]: the original
    affine homotopy starts at f, supporting Federer
    4.1.13, pp. 369–370. *)
Theorem current_affine_homotopy_start (f g:X->Y) (h:Z->Y)
    (hH:is_current_affine_homotopy f g h) x:
  h (@euclidean_block_join R 1%N n (@euclidean_one_embed R 0,x))=f x.
Proof. by rewrite hH subr0 scale1r scale0r addr0. Qed.

(** Source for [current_affine_homotopy_end]: the original
    affine homotopy ends at g, supporting Federer
    4.1.13, pp. 369–370. *)
Theorem current_affine_homotopy_end (f g:X->Y) (h:Z->Y)
    (hH:is_current_affine_homotopy f g h) x:
  h (@euclidean_block_join R 1%N n (@euclidean_one_embed R 1,x))=g x.
Proof. by rewrite hH subrr scale0r scale1r add0r. Qed.
End CurrentAffineHomotopyUP.
