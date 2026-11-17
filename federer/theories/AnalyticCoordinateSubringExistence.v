(** Federer (1969), 3.4.8(1), p. 326:
    the original coordinate germ image exists and is
    unique. The direct image supplies existence only;
    downstream arguments use the independent membership laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticCoordinateSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_coordinate_germ_image_exists]: the
    original coordinate pullback has a set image,
    supporting Q_j in 3.4.8(1), p. 326. *)
Theorem analytic_coordinate_germ_image_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (a:X) (b:Y) (P:analytic_germ_space hNY b->analytic_germ_space hNX a):
  exists Q,is_analytic_coordinate_germ_image P Q.
Proof.
exists (fun alpha=>exists beta,P beta=alpha)=>alpha;reflexivity.
Qed.

(** Source for [analytic_coordinate_germ_image_unique]: the
    original image membership law determines Q_j uniquely,
    supporting 3.4.8(1), p. 326. *)
Theorem analytic_coordinate_germ_image_unique (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (a:X) (b:Y) (P:analytic_germ_space hNY b->analytic_germ_space hNX a)
    (Q U:set (analytic_germ_space hNX a)):
  is_analytic_coordinate_germ_image P Q ->is_analytic_coordinate_germ_image P U ->Q=U.
Proof.
move=>hQ hU;apply/seteqP;split=>alpha hAlpha.
- apply/(hU alpha);exact:(hQ alpha).1 hAlpha.
- apply/(hQ alpha);exact:(hU alpha).1 hAlpha.
Qed.
