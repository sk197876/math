(** Private existence proof for the exact recursive partial
    derivative graph in Federer (1969), 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP PartialFunctionUP NormIteratedDirectionalUP
  NormIteratedDirectionalGraphUP NormIteratedDirectionalLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_iterated_directional_graph_exists]: the
    recursive ordered derivative is a single-valued partial function,
    Federer 3.1.11, p. 223. This proves existence of its
    graph without asserting a derivative at additional points. *)
Theorem norm_iterated_directional_graph_exists (R : realType)
    (X Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) s :
  exists D : partial_function X Y, is_norm_iterated_directional_graph NY A f s D.
Proof.
have hu a y z : has_norm_iterated_directional NY A f s a y ->
    has_norm_iterated_directional NY A f s a z -> y=z.
  exact (@norm_iterated_directional_unique R X Y NY hNY A f s a y z).
exists (@Build_partial_function X Y (has_norm_iterated_directional NY A f s) hu).
by move=>a y.
Qed.
