(** Federer (1969), 4.1.1, p. 346: differentiation of test
    functions before transposition to distributions. A supplied
    linear operator is specified by the actual first differential,
    rather than by a chosen function representative. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_smooth_directional_derivative]: direct
    evaluation law for differentiating a smooth function in a
    fixed direction, supporting D_j phi in Federer 4.1.1,
    p. 346. Standard basis directions give the printed operators. *)
Definition is_smooth_directional_derivative (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (U:set X)
    (E:lmodType R) (ev:E->X->Y)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (v:X) (P:Hom E E):=
  forall f x,U x -> ev (P f) x=
    @ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY [ffun _: 'I_1=>v]
      (@D 1%N x f).
