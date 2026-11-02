(** Private existence proof for D^k f in Federer (1969),
    3.1.11, pp. 218–219. The intrinsic relation is
    single valued, so it gives an exact partial graph.
    This construction is exposed only through its opaque seal. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP PartialFunctionUP
  Hom ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_higher_differential_graph_exists]:
    existence of the exact partial function D^k f, as
    used in Federer 3.1.11, pp. 218–219. This
    proves existence of the graph, not differentiability at
    points where the recursive approximation fails. *)
Theorem norm_higher_differential_graph_exists (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
    (A : X->Prop) (f : X->Y) k :
  exists D : partial_function X (Z k),
    is_norm_higher_differential_graph NX evaluation ZN A f D.
Proof.
have hu a z w : has_norm_higher_differential NX evaluation ZN A f k a z ->
    has_norm_higher_differential NX evaluation ZN A f k a w -> z=w.
  exact: (@norm_higher_differential_unique R X Y NX NY hNX hNY
    Z evaluation ZN hZ A f k a z w).
exists (@Build_partial_function X (Z k)
  (fun a z=>has_norm_higher_differential NX evaluation ZN A f k a z) hu).
by move=> a z.
Qed.
