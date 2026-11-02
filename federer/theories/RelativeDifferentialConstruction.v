(** Private existence proof for the exact relative differential
    graph of Federer (1969), 3.1.22, p. 235. Only its
    sealing module and the assumptions audit may import this file. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP PartialFunctionUP RelativeDifferentialUP RelativeDifferentialUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [relative_norm_differential_graph_exists]: existence
    of the partial function Df(a) justified by uniqueness in
    Federer 3.1.22, p. 235. Its values are exactly
    the relative differentials, each itself defined precisely on
    the tangent cone. No differentiability existence is postulated. *)
Theorem relative_norm_differential_graph_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:X->Prop) (f:X->Y) :
  exists D:partial_function X (partial_function X Y),
    @is_relative_norm_differential_graph R X Y NX NY hNX A S f D.
Proof.
have hu a L M:@has_relative_norm_differential R X Y NX NY hNX A S f a L ->
    @has_relative_norm_differential R X Y NX NY hNX A S f a M -> L=M.
  exact (@relative_norm_differential_unique R X Y NX NY hNX hNY A S f a L M).
exists (@Build_partial_function X (partial_function X Y)
  (fun a L=>@has_relative_norm_differential R X Y NX NY hNX A S f a L) hu).
by move=>a L.
Qed.
