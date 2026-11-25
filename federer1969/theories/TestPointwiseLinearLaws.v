(** Federer (1969), 4.1.3, p. 348: linearity of the
    actual coordinate tensor map is checked pointwise on the
    original test functions. The evaluation laws are those of
    the independently specified test space in 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [test_value_linear_combination]: pointwise vector
    operations on original tests, supporting the canonical
    tensor map of Federer 4.1.3, p. 348. *)
Lemma test_value_linear_combination (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (hE:is_smooth_function_space hNX hNY U ev)
    (c:R) (f g:smooth_test_space hE) (x:X):
  smooth_test_value hE (c*:f+g) x=
    c*:smooth_test_value hE f x+smooth_test_value hE g x.
Proof.
exact:(congr1 (fun a:X->Y=>a x) ((smooth_test_values_linear hE) c f g)).
Qed.
