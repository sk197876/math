(** Federer (1969), 4.1.1, p. 344: support of a linear
    functional is the complement in U of the union of open sets
    on which it annihilates all supported test functions. This
    definition does not assume that the support is compact. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormOpenTopology SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [smooth_functional_annihilation_open]: the open
    sets W in the definition of spt T, Federer 4.1.1, p. 344.
    The evaluation model may represent all smooth functions or
    only compactly supported ones. *)
Definition smooth_functional_annihilation_open (R:realType)
    (X Y:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (E:lmodType R) (ev:E->X->Y) (T:Hom E R^o) (W:set X) :=
  norm_open_family hNX W /\ forall f,
    @smooth_function_support R X Y NX hNX U E ev f `<=` W -> T f=0.

(** Source for [smooth_functional_support]: direct definition
    of spt T, Federer 4.1.1, p. 344, valid both for E' and
    D'. Continuity and compactness are separate assertions. *)
Definition smooth_functional_support (R:realType)
    (X Y:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (E:lmodType R) (ev:E->X->Y) (T:Hom E R^o):set X :=
  [set x|U x /\ ~exists W,smooth_functional_annihilation_open hNX U ev T W /\ W x].
