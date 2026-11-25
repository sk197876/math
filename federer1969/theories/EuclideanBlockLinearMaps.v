(** Federer (1969), 3.1.18, pp. 229–230: linear first and complementary
    coordinates for the product R^v times R^(m-v). We retain the
    existing block identification inside R^(v+l), including l=0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinear FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Blocks.
Variable R:realType.
Variables v l:nat.
Local Notation X:=(R_n R (v+l)).
Local Notation V:=(R_n R v).
Local Notation W:=(R_n R l).

(** Source for [euclidean_first_block]: the projection r in Federer
    3.1.18, p. 229, represented on the isomorphic ambient R^(v+l). *)
Definition euclidean_first_block (x:X):V := [ffun i=>x (lshift l i)].
(** Source for [euclidean_last_block]: complementary source coordinates
    in Federer 3.1.18, p. 229, under the standard block identification. *)
Definition euclidean_last_block (x:X):W := [ffun i=>x (rshift v i)].
(** Source for [euclidean_first_block_linear]: linearity of r,
    supporting the source change in Federer 3.1.18, p. 229. *)
Lemma euclidean_first_block_linear : linear euclidean_first_block.
Proof. move=>c x y; apply/ffunP=>i; by rewrite /euclidean_first_block ?ffunE. Qed.
(** Source for [euclidean_last_block_linear]: linearity of the
    complementary coordinate projection, supporting 3.1.18, p. 229. *)
Lemma euclidean_last_block_linear : linear euclidean_last_block.
Proof. move=>c x y; apply/ffunP=>i; by rewrite /euclidean_last_block ?ffunE. Qed.
(** Source for [euclidean_first_block_map]: boundedness is proved from
    finite dimension; this is the linear projection r in 3.1.18, p. 229. *)
Definition euclidean_first_block_map:Hom X V :=
  @HomMap R X V euclidean_first_block (introT (asboolP _) euclidean_first_block_linear).
(** Source for [euclidean_last_block_map]: the linear complementary
    coordinate map supporting Federer 3.1.18, p. 229. *)
Definition euclidean_last_block_map:Hom X W :=
  @HomMap R X W euclidean_last_block (introT (asboolP _) euclidean_last_block_linear).

(** Source for [euclidean_first_injection]: first-block inclusion
    supporting p* r g and the product identification in 3.1.18, p. 230. *)
Definition euclidean_first_injection (u:V):X := euclidean_block_join (u,(0:W)).
(** Source for [euclidean_last_injection]: last-block inclusion used
    for the W-fibre derivative in Federer 3.1.18, p. 230. *)
Definition euclidean_last_injection (w:W):X := euclidean_block_join ((0:V),w).
(** Source for [euclidean_first_injection_linear]: supporting linearity
    of the first-block inclusion in 3.1.18, p. 230. *)
Lemma euclidean_first_injection_linear : linear euclidean_first_injection.
Proof.
move=>c x y; rewrite /euclidean_first_injection.
have he : ((c*:x+y,(0:W)):(V*W)%type)=c*:(x,(0:W))+(y,(0:W)).
  change ((c*:x+y,(0:W))=(c*:x+y,c*:(0:W)+0)).
  by rewrite scaler0 add0r.
rewrite he; exact (@euclidean_block_join_linear R v l c (x,(0:W)) (y,(0:W))).
Qed.
(** Source for [euclidean_last_injection_linear]: supporting linearity
    of the W-direction inclusion in 3.1.18, p. 230. *)
Lemma euclidean_last_injection_linear : linear euclidean_last_injection.
Proof.
move=>c x y; rewrite /euclidean_last_injection.
have he : (((0:V),c*:x+y):(V*W)%type)=c*:((0:V),x)+((0:V),y).
  change (((0:V),c*:x+y)=(c*:(0:V)+0,c*:x+y)).
  by rewrite scaler0 add0r.
rewrite he; exact (@euclidean_block_join_linear R v l c ((0:V),x) ((0:V),y)).
Qed.
(** Source for [euclidean_first_injection_map]: linear first-block
    inclusion supporting the source chart in 3.1.18, p. 229. *)
Definition euclidean_first_injection_map:Hom V X :=
  @HomMap R V X euclidean_first_injection (introT (asboolP _) euclidean_first_injection_linear).
(** Source for [euclidean_last_injection_map]: linear W-direction
    inclusion used in the fibre argument of 3.1.18, p. 230. *)
Definition euclidean_last_injection_map:Hom W X :=
  @HomMap R W X euclidean_last_injection (introT (asboolP _) euclidean_last_injection_linear).

(** Source for [euclidean_first_block_injectionK]: r(v,0)=v,
    supporting the source-coordinate correction in 3.1.18, p. 229. *)
Lemma euclidean_first_block_injectionK : cancel euclidean_first_injection euclidean_first_block.
Proof. move=>u; exact (congr1 fst (@euclidean_block_joinK R v l (u,(0:W)))). Qed.
(** Source for [euclidean_last_block_injectionK]: the last block of
    (0,w) equals w, supporting 3.1.18, p. 230. *)
Lemma euclidean_last_block_injectionK : cancel euclidean_last_injection euclidean_last_block.
Proof. move=>w; exact (congr1 snd (@euclidean_block_joinK R v l ((0:V),w))). Qed.
(** Source for [euclidean_first_block_last_injection]: r(0,w)=0,
    the kernel condition for W-directions in 3.1.18, p. 230. *)
Lemma euclidean_first_block_last_injection w : euclidean_first_block (euclidean_last_injection w)=0.
Proof. exact (congr1 fst (@euclidean_block_joinK R v l ((0:V),w))). Qed.
(** Source for [euclidean_last_block_first_injection]: the first-block
    correction leaves complementary coordinates fixed, supporting the
    source chart in Federer 3.1.18, p. 229. *)
Lemma euclidean_last_block_first_injection u : euclidean_last_block (euclidean_first_injection u)=0.
Proof. exact (congr1 snd (@euclidean_block_joinK R v l (u,(0:W)))). Qed.
(** Source for [euclidean_block_linear_decomposition]: (v,w)=(v,0)+(0,w),
    the product-coordinate identity supporting 3.1.18, pp. 229–230. *)
Lemma euclidean_block_linear_decomposition x :
  x=euclidean_first_injection (euclidean_first_block x)+
    euclidean_last_injection (euclidean_last_block x).
Proof.
have hh:=@euclidean_block_join_linear R v l 1
  (euclidean_first_block x,(0:W)) ((0:V),euclidean_last_block x).
rewrite !scale1r in hh.
have he : (euclidean_first_block x,(0:W))+((0:V),euclidean_last_block x)=euclidean_block_split x.
  change ((euclidean_first_block x+0,0+euclidean_last_block x)=
    (euclidean_first_block x,euclidean_last_block x)).
  by rewrite addr0 add0r.
by rewrite he euclidean_block_splitK in hh.
Qed.
End Blocks.
