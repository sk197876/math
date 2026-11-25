(** Federer (1969), 4.1.7, pp. 355–359: a local
    original test operator gives a transpose that
    shrinks functional support. This uses the original
    local annihilation definition of 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormOpenTopology SmoothFunctionSupport FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [test_dual_operator_support_subset]:
    support locality of the original test transpose,
    supporting the current operations and proper
    pushforward of Federer 4.1.7, pp. 355–359. *)
Theorem test_dual_operator_support_subset (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (E F:lmodType R) (ev:E->X->Y) (fv:F->X->Z)
    (P:Hom E F) (T:Hom F R^o) (S:Hom E R^o):
  (forall f,S f=T (P f))->
  (forall f,@smooth_function_support R X Z NX hNX U F fv (P f) `<=`
    @smooth_function_support R X Y NX hNX U E ev f)->
  @smooth_functional_support R X Y NX hNX U E ev S `<=`
    @smooth_functional_support R X Z NX hNX U F fv T.
Proof.
move=>hAction hSupport x [hx hNot];split=>//.
move=>[W [[hW hZero] hxW]];apply:hNot;exists W;split=>//;split=>//f hf.
rewrite hAction;apply:hZero=>y hy;exact:(hf y (hSupport f y hy)).
Qed.
