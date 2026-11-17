(** Federer (1969), 3.4.8(1), p. 326:
    Q_j is the image of the original coordinate
    pullback on analytic germs. The membership law
    specifies that image independently of a set construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_coordinate_germ_image]: the original
    image subring Q_j, 3.4.8(1), p. 326. Its
    membership law uses every germ in the original
    coordinate source; no closedness or selected image is assumed. *)
Definition is_analytic_coordinate_germ_image (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (a:X) (b:Y) (P:analytic_germ_space hNY b->analytic_germ_space hNX a)
    (Q:set (analytic_germ_space hNX a)):Prop:=
  forall alpha,Q alpha <->exists beta,P beta=alpha.
