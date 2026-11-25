(** Federer (1969), 4.1.9, p. 363: the space
    differential of h_t is the original differential
    of h composed with its second block injection.
    This is the preceding chain rule, with U retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal NormDifferentialChain
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  CurrentMapDifferential CurrentClassOneMapDifferential CurrentCartesianPointInclusion
  CurrentHomotopyUP CurrentHomotopyGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentHomotopySliceDifferential.
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
Hypothesis hClass:@is_current_homotopy_class R n nu A U V f g h 1%N.
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation slice := (@current_homotopy_slice_map R n nu h).
Local Notation Q := (@euclidean_last_injection_map R 1%N n).

(** Source for [current_homotopy_slice_differential]:
    Dh_t(x)=Dh(t,x) composed with Q on every
    original t in A and x in U, supporting the
    displayed differential decomposition in Federer
    4.1.9, p. 363. *)
Theorem current_homotopy_slice_differential t x:
  A t->U x->@current_map_differential R n nu U (slice t) x=
    hom_comp (@current_map_differential R (1+n)%N nu AU h
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x))) Q.
Proof.
move=>ht hx.
have hGeometry:=hClass.1.
pose inclusion:=@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t).
have hInclusion:=@current_cartesian_point_inclusion_differential R 1%N n U
  (@current_homotopy_source_open R n nu A U V f g h hGeometry)
  (@euclidean_one_embed R t) x hx.
have hImage y (hy:U y):AU (inclusion y).
  exact:(@current_homotopy_join_member R n A U t y ht hy).
have hDh:=@current_class_one_map_differential R (1+n)%N nu AU h hClass.2
  (inclusion x) (hImage x hx).
have hChain:=@norm_differential_chain R X Z Y NX NZ NY hNX hNZ hNY U AU
  inclusion h x Q (@current_map_differential R (1+n)%N nu AU h (inclusion x))
  hInclusion hDh.
apply:(@current_map_differential_unique R n nu U (slice t) x).
apply:(@norm_differential_restrict R X Y NX NY
  (fun y=>U y /\ AU (inclusion y)) U (slice t) x _).
- move=>y hy;exact:conj hy (hImage y hy).
- exact:(@current_homotopy_source_open R n nu A U V f g h hGeometry x hx).
- exact:hChain.
Qed.
End CurrentHomotopySliceDifferential.
