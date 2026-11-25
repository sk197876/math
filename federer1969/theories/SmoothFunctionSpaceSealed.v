(** Federer (1969), 4.1.1, pp. 343–344: opaque E(U,Y), exposing
    only its vector space, evaluation and proved realization laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP SmoothFunctionSpaceUP SmoothFunctionSpaceConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SmoothFunctionSpaceSignature.
(** Source for [space]: the abstract smooth-function space
    E(U,Y), Federer 4.1.1, p. 343. *)
Parameter space : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X), (forall x,U x -> norm_domain_interior NX U x) -> lmodType R.
(** Source for [value]: evaluation of E(U,Y) on its open domain,
    Federer 4.1.1, pp. 343–344. *)
Parameter value : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x -> norm_domain_interior NX U x),
    @space R X Y NX NY hNX hNY U hU -> X->Y.
(** Source for [laws]: the independent evaluation laws of E(U,Y)
    are proved, Federer 4.1.1, pp. 343–344. *)
Parameter laws : forall (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x -> norm_domain_interior NX U x),
    is_smooth_function_space hNX hNY U (@value R X Y NX NY hNX hNY U hU).
End SmoothFunctionSpaceSignature.

Module SmoothFunctionSpace : SmoothFunctionSpaceSignature.
(** Source for [space]: the hidden proved smooth-function
    carrier of E(U,Y), Federer 4.1.1, p. 343. *)
Definition space (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x -> norm_domain_interior NX U x) : lmodType R :=
  [the lmodType R of @SmoothFunctionWitness R X Y NX NY hNX hNY U hU].
(** Source for [value]: the private evaluation witness for
    E(U,Y), Federer 4.1.1, p. 343. *)
Definition value (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x -> norm_domain_interior NX U x) :
    @space R X Y NX NY hNX hNY U hU -> X->Y :=
  @smooth_function_value_witness R X Y NX NY hNX hNY U hU.
(** Source for [laws]: the hidden witness satisfies precisely
    the independent E(U,Y) specification, Federer 4.1.1, p. 343. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x -> norm_domain_interior NX U x) :
    is_smooth_function_space hNX hNY U (@value R X Y NX NY hNX hNY U hU).
Proof. exact:(@smooth_function_space_witness R X Y NX NY hNX hNY U hU). Qed.
End SmoothFunctionSpace.
