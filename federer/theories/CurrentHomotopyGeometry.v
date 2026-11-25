(** Federer (1969), 4.1.9, p. 363: the original
    interval and endpoint geometry of a given homotopy.
    Reuse the actual block and scalar-coordinate inverse laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanCartesianMap CurrentHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_homotopy_closed_time_band]: the
    original interval A contains every time between
    zero and one, supporting the closed-cylinder
    hypothesis in Federer 4.1.9, p. 363. *)
Lemma current_homotopy_closed_time_band (R:realType) (A:set R)
    (hA:@is_homotopy_parameter_interval R A) t:
  0<=t<=1->A t.
Proof.
move=>ht.
exact:(@homotopy_parameter_between R A hA 0 1 t
  (@homotopy_parameter_zero R A hA) (@homotopy_parameter_one R A hA) ht).
Qed.

(** Source for [current_homotopy_join_member]: an original
    t in A and x in U determine their
    original point (t,x) in A times U,
    supporting Federer 4.1.9, p. 363, by
    2.6.5, p. 120. *)
Lemma current_homotopy_join_member (R:realType) n (A:set R) (U:set (R_n R n))
    (t:R) (x:R_n R n):
  A t->U x->@current_homotopy_product_domain R n A U
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Proof.
move=>ht hx.
change (A (@euclidean_one_project R
      (@euclidean_block_split R 1%N n
        (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))).1) /\
    U (@euclidean_block_split R 1%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))).2).
rewrite euclidean_block_joinK euclidean_one_embedK.
exact:conj ht hx.
Qed.

(** Source for [current_homotopy_slice_image]: every original
    h_t maps U into V for t in A,
    Federer 4.1.9, p. 363. *)
Theorem current_homotopy_slice_image (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hGeometry:@is_current_homotopy_geometry R n nu A U V f g h) t:
  A t->forall x,U x->V (@current_homotopy_slice_map R n nu h t x).
Proof.
move=>ht x hx.
exact:(@current_homotopy_image R n nu A U V f g h hGeometry
  (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))
  (@current_homotopy_join_member R n A U t x ht hx)).
Qed.

(** Source for [current_homotopy_endpoint_images]: the original
    endpoint maps f and g map U into V,
    Federer 4.1.9, p. 363. This follows from
    the given homotopy image and endpoint laws. *)
Theorem current_homotopy_endpoint_images (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hGeometry:@is_current_homotopy_geometry R n nu A U V f g h):
  (forall x,U x->V (f x)) /\ (forall x,U x->V (g x)).
Proof.
have hA:=@current_homotopy_parameter_interval R n nu A U V f g h hGeometry.
split=>x hx.
- have hImage:=@current_homotopy_slice_image R n nu A U V f g h hGeometry 0
    (@homotopy_parameter_zero R A hA) x hx.
  by rewrite (@current_homotopy_start R n nu A U V f g h hGeometry x hx) in hImage.
- have hImage:=@current_homotopy_slice_image R n nu A U V f g h hGeometry 1
    (@homotopy_parameter_one R A hA) x hx.
  by rewrite (@current_homotopy_end R n nu A U V f g h hGeometry x hx) in hImage.
Qed.
