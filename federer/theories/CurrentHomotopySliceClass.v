(** Federer (1969), 4.1.9, p. 363: each fixed-time
    slice has the original homotopy's class. The endpoint
    identities concern the given maps on U only.
    Reuse the preceding affine inclusion and composition laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate CurrentCartesianPointInclusion
  CurrentHomotopyUP CurrentHomotopyGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopySliceClass.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation slice := (@current_homotopy_slice_map R n nu h).

(** Source for [current_homotopy_slice_class]: the original
    h_t is of class r on U for each t in A,
    supporting Federer 4.1.9, p. 363, by
    the composition rule of 3.1.11, p. 220. *)
Theorem current_homotopy_slice_class r:
  @is_current_homotopy_class R n nu A U V f g h r ->
  forall t,A t->norm_class hNX hNY U (slice t) r.
Proof.
move=>[hGeometry hClass] t ht.
pose inclusion:=@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t).
have hInclusion:=@current_cartesian_point_inclusion_smooth R 1%N n U
  (@current_homotopy_source_open R n nu A U V f g h hGeometry) (@euclidean_one_embed R t).
have hImage x (hx:U x):AU (inclusion x).
  exact:(@current_homotopy_join_member R n A U t x ht hx).
exact:(@norm_class_compose_on R X Z Y NX NZ NY hNX hNZ hNY U AU
  inclusion h r hImage (hInclusion r) hClass).
Qed.

(** Source for [current_smooth_homotopy_slice_class]: every
    original slice of the smooth homotopy is smooth
    on U, supporting the deformation-chain formulas
    of Federer 4.1.9, p. 363. *)
Theorem current_smooth_homotopy_slice_class:
  @is_smooth_current_homotopy R n nu A U V f g h ->
  forall t,A t->norm_class_all_orders hNX hNY U (slice t).
Proof.
move=>[hGeometry hClass] t ht r.
exact:(current_homotopy_slice_class (conj hGeometry (hClass r)) ht).
Qed.

(** Source for [current_homotopy_endpoint_classes]: f=h_0
    and g=h_1 on the actual U inherit class r,
    supporting the endpoint pullbacks in Federer
    4.1.9, p. 363. No equality outside U is assumed. *)
Theorem current_homotopy_endpoint_classes r:
  @is_current_homotopy_class R n nu A U V f g h r ->
  norm_class hNX hNY U f r /\ norm_class hNX hNY U g r.
Proof.
move=>hClass.
have hGeometry:=hClass.1.
have hA:=@current_homotopy_parameter_interval R n nu A U V f g h hGeometry.
split.
- apply:(@norm_class_domain_agreement R X Y NX NY hNX hNY U (slice 0) f r).
  + exact:(@current_homotopy_start R n nu A U V f g h hGeometry).
  + exact:(current_homotopy_slice_class hClass (@homotopy_parameter_zero R A hA)).
- apply:(@norm_class_domain_agreement R X Y NX NY hNX hNY U (slice 1) g r).
  + exact:(@current_homotopy_end R n nu A U V f g h hGeometry).
  + exact:(current_homotopy_slice_class hClass (@homotopy_parameter_one R A hA)).
Qed.

(** Source for [current_smooth_homotopy_endpoint_classes]: the
    original endpoint maps of a smooth homotopy are
    smooth on U, supporting Federer 4.1.9,
    p. 363, with every original domain retained. *)
Theorem current_smooth_homotopy_endpoint_classes:
  @is_smooth_current_homotopy R n nu A U V f g h ->
  norm_class_all_orders hNX hNY U f /\ norm_class_all_orders hNX hNY U g.
Proof.
move=>[hGeometry hClass];split=>r.
- exact:(current_homotopy_endpoint_classes (conj hGeometry (hClass r))).1.
- exact:(current_homotopy_endpoint_classes (conj hGeometry (hClass r))).2.
Qed.
End CurrentHomotopySliceClass.
