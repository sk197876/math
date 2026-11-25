(** Federer (1969), 4.1.2, p. 347: test-space
    smoothing is independently specified by its
    agreement with the actual smooth-space operator
    after the original inclusion D -> E. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP SmoothFunctionSpaceUP SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_test_smoothing_family]: the same original
    Phi_epsilon*f is a test function when f
    is a test function, Federer 4.1.2,
    p. 347. Its linear values
    are specified before existence and opaque sealing. *)
Definition is_test_smoothing_family (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev) (P:R->Hom E E)
    (Q:R->Hom (smooth_test_space hE) (smooth_test_space hE)):=
  forall e:R,0<e ->forall f:smooth_test_space hE,
    smooth_test_inclusion hE (Q e f)= P e (smooth_test_inclusion hE f).
