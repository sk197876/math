(** Federer (1969), 4.1.2, p. 348: test
    cutoffs on an arbitrary open U are eventually
    one on each compact subset. Their exact original
    values, rather than a construction, specify the sequence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_test_cutoff_exhaustion]: the sequence
    omega_j in the last paragraph of Federer 4.1.2,
    p. 348. Every member is an actual
    scalar test, and equality to one is eventual
    on every original compact subset of U. *)
Definition is_test_cutoff_exhaustion (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (E:lmodType R) (ev:E->X->R^o)
    (hE:is_smooth_function_space hNX (@scalar_absolute_value_norm R) U ev)
    (omega:nat->smooth_test_space hE):Prop:=
  forall K:smooth_compact_set hNX U,exists v:nat,(0<v)%N /\
    forall j,(v<=j)%N ->forall x,smooth_compact_carrier K x ->
      smooth_test_value hE (omega j) x= 1.
