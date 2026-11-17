(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    Q_j is the image of the original coordinate
    pullback on analytic germs. The membership law
    specifies that image independently of a set construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP RealNormUP HolomorphicGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_coordinate_germ_image]: the original
    image subring Q_j, 3.4.8(1), p. 326. Its
    membership law uses every germ in the original
    coordinate source; no closedness or selected image is assumed. *)
Definition is_holomorphic_coordinate_germ_image (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (a:X) (b:Y) (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a)
    (Q:set (holomorphic_germ_space hNX a)):Prop:=
  forall alpha,Q alpha <->exists beta,P beta=alpha.
