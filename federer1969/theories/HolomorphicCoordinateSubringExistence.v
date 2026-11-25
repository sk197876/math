(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    the original coordinate germ image exists and is
    unique. The direct image supplies existence only;
    downstream arguments use the independent membership laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP RealNormUP HolomorphicGermUP HolomorphicCoordinateSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_coordinate_germ_image_exists]: the
    original coordinate pullback has a set image,
    supporting Q_j in 3.4.8(1), p. 326. *)
Theorem holomorphic_coordinate_germ_image_exists (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (a:X) (b:Y) (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  exists Q,is_holomorphic_coordinate_germ_image P Q.
Proof.
exists (fun alpha=>exists beta,P beta=alpha)=>alpha;reflexivity.
Qed.

(** Source for [holomorphic_coordinate_germ_image_unique]: the
    original image membership law determines Q_j uniquely,
    supporting 3.4.8(1), p. 326. *)
Theorem holomorphic_coordinate_germ_image_unique (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (a:X) (b:Y) (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a)
    (Q U:set (holomorphic_germ_space hNX a)):
  is_holomorphic_coordinate_germ_image P Q ->is_holomorphic_coordinate_germ_image P U ->Q=U.
Proof.
move=>hQ hU;apply/seteqP;split=>alpha hAlpha.
- apply/(hU alpha);exact:(hQ alpha).1 hAlpha.
- apply/(hQ alpha);exact:(hU alpha).1 hAlpha.
Qed.
