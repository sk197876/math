(** Private existence proof for the differential graph of Federer (1969),
    3.1.1, p. 209. Directional uniqueness proves that the approximation
    relation is single valued. No existence of a derivative is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP
  NormDifferentialUP NormDifferentialDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_differential_graph_exists]: supporting existence of
    the partial function Df in Federer 3.1.1, p. 209. Its graph consists
    exactly of the unique differentials at differentiability points. *)
Theorem norm_differential_graph_exists (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) :
  exists D : partial_function X (Hom X Y),
    is_norm_differential_graph NX NY A f D.
Proof.
have hu : forall a L M, has_norm_differential NX NY A f a L ->
    has_norm_differential NX NY A f a M -> L=M.
  move=> a L M; exact: (@norm_differential_unique R X Y NX NY hNX hNY A f a L M).
exists (@Build_partial_function X (Hom X Y)
  (fun a L => has_norm_differential NX NY A f a L) hu).
by move=> a L.
Qed.
