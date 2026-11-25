(** Private existence witnesses for the exact approximate differential
    and approximate partial derivative graphs, Federer (1969), 3.1.2,
    p. 212. Single-valuedness is proved; no existence at every point is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations RealNormUP PartialFunctionUP
  ApproximateDifferentialUP ApproximateDifferentialUniqueness
  ApproximatePartialDerivativeUP ApproximatePartialDerivativeUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [approximate_differential_graph_exists]: existence of the
    partial function ap Df specified in Federer 3.1.2, p. 212. *)
Theorem approximate_differential_graph_exists (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop) (f : R_n R n -> Y) :
  exists D : partial_function (R_n R n) (Hom (R_n R n) Y),
    is_approximate_differential_graph NY A f D.
Proof.
have hu : forall a L M, has_approximate_differential NY A f a L ->
    has_approximate_differential NY A f a M -> L=M.
  move=> a L M; exact: (@approximate_differential_unique R n Y NY hNY A f a L M).
exists (@Build_partial_function _ _ (fun a L => has_approximate_differential NY A f a L) hu).
by move=> a L.
Qed.

(** Source for [approximate_partial_derivative_graph_exists]: existence of
    the partial function ap D_i f specified in Federer 3.1.2, p. 212. *)
Theorem approximate_partial_derivative_graph_exists (R : realType) n (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R_n R n -> Prop)
    (f : R_n R n -> Y) (i : 'I_n) :
  exists D : partial_function (R_n R n) Y,
    is_approximate_partial_derivative_graph hNY A f i D.
Proof.
have hu : forall a u v, has_approximate_partial_derivative hNY A f a i u ->
    has_approximate_partial_derivative hNY A f a i v -> u=v.
  move=> a u v; exact: (@approximate_partial_derivative_unique R n Y NY hNY A f a i u v).
exists (@Build_partial_function _ _
  (fun a v => has_approximate_partial_derivative hNY A f a i v) hu).
by move=> a v.
Qed.
