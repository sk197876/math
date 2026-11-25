(** Federer (1969), 4.1.9, p. 363: split the
    original differential into its time and space
    terms. The chain rule identifies the space
    term; linearity gives the printed decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockCoordinates EuclideanBlockLinearMaps
  CurrentMapDifferential CurrentCartesianAffineSlice CurrentHomotopyUP
  CurrentHomotopyTimeVelocity CurrentHomotopySliceDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyDifferential.
Variable R:realType.
Variables n nu:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu).

(** Source for [current_homotopy_differential]: the displayed
    identity Dh(t,x)(v,w)=v h-dot_t(x)+Dh_t(x)w,
    Federer 4.1.9, p. 363. It holds at every
    original t and x, including zero-dimensional
    source or target, under the original class-one condition. *)
Theorem current_homotopy_differential
    (hClass:@is_current_homotopy_class R n nu A U V f g h 1%N)
    t x (v:R) (w:R_n R n):
  A t->U x->
  @current_map_differential R (1+n)%N nu (@current_homotopy_product_domain R n A U) h
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R v,w))=
  v*:(@current_homotopy_time_velocity R n nu A U h t x)+
    @current_map_differential R n nu U (@current_homotopy_slice_map R n nu h t) x w.
Proof.
move=>ht hx.
have hTime:@euclidean_one_embed R v=v*:(@euclidean_one_embed R 1).
  apply/ffunP=>k;rewrite /euclidean_one_embed !ffunE.
  change (v=v*1);by rewrite mulr1.
rewrite (@current_homotopy_slice_differential R n nu A U V f g h hClass t x ht hx)
  hom_compE (@current_cartesian_join_affine R 1%N n (@euclidean_one_embed R v) w).
by rewrite /current_homotopy_time_velocity hTime linearD !linearZ.
Qed.

(** Source for [current_positive_class_homotopy_differential]:
    the same printed differential decomposition holds
    for every class r at least one, Federer
    4.1.9, p. 363. Lowering the original class
    uses 3.1.11, p. 220, on the same map and domain. *)
Theorem current_positive_class_homotopy_differential r
    (hClass:@is_current_homotopy_class R n nu A U V f g h r):
  (1<=r)%N->forall t x (v:R) (w:R_n R n),A t->U x->
  @current_map_differential R (1+n)%N nu (@current_homotopy_product_domain R n A U) h
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))
    (@euclidean_block_join R 1%N n (@euclidean_one_embed R v,w))=
  v*:(@current_homotopy_time_velocity R n nu A U h t x)+
    @current_map_differential R n nu U (@current_homotopy_slice_map R n nu h t) x w.
Proof.
move=>hr.
have hOne:@is_current_homotopy_class R n nu A U V f g h 1%N.
  split;first exact:hClass.1.
  exact:(norm_class_lower hr hClass.2).
exact:(current_homotopy_differential hOne).
Qed.
End CurrentHomotopyDifferential.
