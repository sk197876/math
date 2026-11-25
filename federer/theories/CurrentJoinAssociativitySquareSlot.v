(** Federer (1969), 4.1.11, p. 366: apply
    the original square map f or g while retaining
    all three original spatial factors. These are
    aliases of the preceding Cartesian map operation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentCartesianMapClass CurrentJoinSliceMapClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativitySquareSlot.
Variable R:realType.
Variable n:nat.
Variable h:R_n R 2%N->R_n R 3%N.
Local Notation Id := (fun x:R_n R n=>x).

(** Source for [current_join_assoc_square_inner]: the original
    h times identity acts on square times T, supporting
    Federer 4.1.11, p. 366. *)
Definition current_join_assoc_square_inner:R_n R (2+n)%N->R_n R (3+n)%N:=
  @euclidean_cartesian_map R 2%N n 3%N n h Id.

(** Source for [current_join_assoc_square_middle]: retain S
    beside the original inner square image, supporting
    Federer 4.1.11, p. 366. *)
Definition current_join_assoc_square_middle:R_n R (n+(2+n))%N->R_n R (n+(3+n))%N:=
  @euclidean_cartesian_map R n (2+n)%N n (3+n)%N Id current_join_assoc_square_inner.

(** Source for [current_join_assoc_square_slot]: retain R
    beside the original middle image, supporting the
    common H argument in Federer 4.1.11, p. 366. *)
Definition current_join_assoc_square_slot:R_n R (n+(n+(2+n)))%N->R_n R (n+(n+(3+n)))%N:=
  @euclidean_cartesian_map R n (n+(2+n))%N n (n+(3+n))%N Id current_join_assoc_square_middle.

Hypothesis hh:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
  (inner_norm_real_norm (@euclidean_inner_productP R 3%N)) (fun _=>True) h.
Local Notation hId := (@current_join_slice_identity_smooth R n).

(** Source for [current_join_assoc_square_inner_smooth]: the
    original inner square image map is smooth by the
    preceding Cartesian calculus, Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_square_inner_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (2+n)%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (3+n)%N))
    (fun _=>True) current_join_assoc_square_inner.
Proof. exact:(@current_cartesian_map_smooth R 2%N n 3%N n h Id hh hId). Qed.

(** Source for [current_join_assoc_square_middle_smooth]: the
    original middle square image map is smooth, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_square_middle_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(2+n))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(3+n))%N))
    (fun _=>True) current_join_assoc_square_middle.
Proof.
exact:(@current_cartesian_map_smooth R n (2+n)%N n (3+n)%N Id current_join_assoc_square_inner
  hId current_join_assoc_square_inner_smooth).
Qed.

(** Source for [current_join_assoc_square_slot_smooth]: the
    original full common-source square image map is smooth,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_square_slot_smooth:
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R (n+(n+(2+n)))%N))
    (inner_norm_real_norm (@euclidean_inner_productP R (n+(n+(3+n)))%N))
    (fun _=>True) current_join_assoc_square_slot.
Proof.
exact:(@current_cartesian_map_smooth R n (n+(2+n))%N n (n+(3+n))%N Id current_join_assoc_square_middle
  hId current_join_assoc_square_middle_smooth).
Qed.
End CurrentJoinAssociativitySquareSlot.
