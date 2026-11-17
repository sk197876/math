(** Federer (1969), 3.4.12, p. 339: first and last complex
    coordinate blocks, their inclusions and inverse identities. Apply
    the existing finite concatenation and linear-map laws. These
    interfaces retain the prescribed original prefix coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom FieldBlockCoordinates FieldBlockLinear FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Blocks.
Variable R:fieldType.
Variables v l:nat.
Local Notation X:=(coordinate_space R (v+l)).
Local Notation V:=(coordinate_space R v).
Local Notation W:=(coordinate_space R l).

(** Source for [field_first_block]: the projection r in Federer
    3.1.18, p. 229, represented on the isomorphic ambient R^(v+l). *)
Definition field_first_block (x:X):V := [ffun i=>x (lshift l i)].
(** Source for [field_last_block]: complementary source coordinates
    in Federer 3.1.18, p. 229, under the standard block identification. *)
Definition field_last_block (x:X):W := [ffun i=>x (rshift v i)].
(** Source for [field_first_block_linear]: linearity of r,
    supporting the source change in Federer 3.1.18, p. 229. *)
Lemma field_first_block_linear : linear field_first_block.
Proof. move=>c x y; apply/ffunP=>i; by rewrite /field_first_block ?ffunE. Qed.
(** Source for [field_last_block_linear]: linearity of the
    complementary coordinate projection, supporting 3.1.18, p. 229. *)
Lemma field_last_block_linear : linear field_last_block.
Proof. move=>c x y; apply/ffunP=>i; by rewrite /field_last_block ?ffunE. Qed.
(** Source for [field_first_block_map]: boundedness is proved from
    finite dimension; this is the linear projection r in 3.1.18, p. 229. *)
Definition field_first_block_map:Hom X V :=
  @HomMap R X V field_first_block (introT (asboolP _) field_first_block_linear).
(** Source for [field_last_block_map]: the linear complementary
    coordinate map supporting Federer 3.1.18, p. 229. *)
Definition field_last_block_map:Hom X W :=
  @HomMap R X W field_last_block (introT (asboolP _) field_last_block_linear).

(** Source for [field_first_injection]: first-block inclusion
    supporting p* r g and the product identification in 3.1.18, p. 230. *)
Definition field_first_injection (u:V):X := field_block_join (u,(0:W)).
(** Source for [field_last_injection]: last-block inclusion used
    for the W-fibre derivative in Federer 3.1.18, p. 230. *)
Definition field_last_injection (w:W):X := field_block_join ((0:V),w).
(** Source for [field_first_injection_linear]: supporting linearity
    of the first-block inclusion in 3.1.18, p. 230. *)
Lemma field_first_injection_linear : linear field_first_injection.
Proof.
move=>c x y; rewrite /field_first_injection.
have he : ((c*:x+y,(0:W)):(V*W)%type)=c*:(x,(0:W))+(y,(0:W)).
  change ((c*:x+y,(0:W))=(c*:x+y,c*:(0:W)+0)).
  by rewrite scaler0 add0r.
rewrite he; exact (@field_block_join_linear R v l c (x,(0:W)) (y,(0:W))).
Qed.
(** Source for [field_last_injection_linear]: supporting linearity
    of the W-direction inclusion in 3.1.18, p. 230. *)
Lemma field_last_injection_linear : linear field_last_injection.
Proof.
move=>c x y; rewrite /field_last_injection.
have he : (((0:V),c*:x+y):(V*W)%type)=c*:((0:V),x)+((0:V),y).
  change (((0:V),c*:x+y)=(c*:(0:V)+0,c*:x+y)).
  by rewrite scaler0 add0r.
rewrite he; exact (@field_block_join_linear R v l c ((0:V),x) ((0:V),y)).
Qed.
(** Source for [field_first_injection_map]: linear first-block
    inclusion supporting the source chart in 3.1.18, p. 229. *)
Definition field_first_injection_map:Hom V X :=
  @HomMap R V X field_first_injection (introT (asboolP _) field_first_injection_linear).
(** Source for [field_last_injection_map]: linear W-direction
    inclusion used in the fibre argument of 3.1.18, p. 230. *)
Definition field_last_injection_map:Hom W X :=
  @HomMap R W X field_last_injection (introT (asboolP _) field_last_injection_linear).

(** Source for [field_first_block_injectionK]: r(v,0)=v,
    supporting the source-coordinate correction in 3.1.18, p. 229. *)
Lemma field_first_block_injectionK : cancel field_first_injection field_first_block.
Proof. move=>u; exact (congr1 fst (@field_block_joinK R v l (u,(0:W)))). Qed.
(** Source for [field_last_block_injectionK]: the last block of
    (0,w) equals w, supporting 3.1.18, p. 230. *)
Lemma field_last_block_injectionK : cancel field_last_injection field_last_block.
Proof. move=>w; exact (congr1 snd (@field_block_joinK R v l ((0:V),w))). Qed.
(** Source for [field_first_block_last_injection]: r(0,w)=0,
    the kernel condition for W-directions in 3.1.18, p. 230. *)
Lemma field_first_block_last_injection w : field_first_block (field_last_injection w)=0.
Proof. exact (congr1 fst (@field_block_joinK R v l ((0:V),w))). Qed.
(** Source for [field_last_block_first_injection]: the first-block
    correction leaves complementary coordinates fixed, supporting the
    source chart in Federer 3.1.18, p. 229. *)
Lemma field_last_block_first_injection u : field_last_block (field_first_injection u)=0.
Proof. exact (congr1 snd (@field_block_joinK R v l (u,(0:W)))). Qed.
(** Source for [field_block_linear_decomposition]: (v,w)=(v,0)+(0,w),
    the product-coordinate identity supporting 3.1.18, pp. 229–230. *)
Lemma field_block_linear_decomposition x :
  x=field_first_injection (field_first_block x)+
    field_last_injection (field_last_block x).
Proof.
have hh:=@field_block_join_linear R v l 1
  (field_first_block x,(0:W)) ((0:V),field_last_block x).
rewrite !scale1r in hh.
have he : (field_first_block x,(0:W))+((0:V),field_last_block x)=field_block_split x.
  change ((field_first_block x+0,0+field_last_block x)=
    (field_first_block x,field_last_block x)).
  by rewrite addr0 add0r.
by rewrite he field_block_splitK in hh.
Qed.
End Blocks.
