(** Federer (1969), 2.10.47, p. 204: repeated subdivision of one compact
    unit cube into 2^n congruent cubes. Specify all level-j cubes by their
    coordinate endpoints; existence and opaque selection follow separately.
    Each side has 2^j cells. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [dyadic_cube_indices]: finite coordinate
    indices for H_j in 2.10.47, p. 204. The
    empty coordinate family is retained when n=0. *)
Definition dyadic_cube_indices n j : finType :=
  [the finType of {ffun 'I_n -> 'I_((2^j)%N)}].

(** Source for [is_dyadic_cube_grid]: abstract coordinate
    law for the level-j closed cubes of 2.10.47,
    p. 204, with a prescribed lower corner a. The
    law determines sets, without assuming covering, nesting,
    disjoint interiors or diameter estimates as axioms. *)
Definition is_dyadic_cube_grid (R : realType) n (a : R_n R n)
    (Q : forall j, dyadic_cube_indices n j ->
      set (inner_metric_space (@euclidean_inner_productP R n))) : Prop :=
  forall j s x, Q j s x <-> forall i,
    a i+(s i)%:R/((2^j)%N)%:R<=x i<=a i+((s i).+1)%:R/((2^j)%N)%:R.
