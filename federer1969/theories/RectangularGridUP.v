(** Federer (1969), 2.10.39, printed p. 199: subdivide the longer sides of
    the enclosing box and use centres of the resulting small boxes. Specify
    a grid centre by its orthonormal coordinates; no arithmetic construction
    is exposed. Source context and spherical-covering background:
    ScalarSubdivisionCount.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [rectangular_grid_indices]: supporting
    finite Cartesian product of side-cell indices for
    the subdivision in 2.10.39, p. 199.
    The dependent domain records each side's own count. *)
Definition rectangular_grid_indices n (count : 'I_n -> nat) : finType :=
  [the finType of {dffun forall i : 'I_n, 'I_(count i)}].

(** Source for [is_rectangular_grid_centres]: supporting
    coordinate specification for the small-box centres
    in 2.10.39, p. 199. Each coordinate is
    the midpoint of the corresponding pair of side nodes;
    covering and radius estimates are derived separately. *)
Definition is_rectangular_grid_centres (R : realType) n (origin : R_n R n)
    (axis : 'I_n -> R_n R n) (count : 'I_n -> nat)
    (node : 'I_n -> nat -> R)
    (centre : rectangular_grid_indices count -> R_n R n) : Prop :=
  forall s i, euclidean_inner_product (centre s-origin) (axis i)=
    (node i (s i)+node i (s i).+1)/2.
