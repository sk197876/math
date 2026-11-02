(** Federer (1969), 2.10.44, printed p. 202, first example:
    mu(x)=sup{|x_1|,|x_2|} on R^2. Specify the coordinate supremum by the
    existing least-uniform-bound laws before proving a norm witness. The
    implementation will be sealed; its real norm laws and the printed
    two-coordinate evaluation are derived from this specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates UniformFunctionNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_plane_supremum_norm]: direct abstract
    supremum specification of mu in 2.10.44,
    p. 202. The norm is the least nonnegative
    bound on the two absolute coordinate values.
    No norm laws or existence are postulated. *)
Definition is_plane_supremum_norm (R : realType) (N : R_n R 2 -> R) :=
  forall x : R_n R 2, is_uniform_function_norm (fun i : 'I_2=>x i) (N x).
