(** Federer (1969), 4.1.27, p. 384: prove
    existence of the independently specified prefix-product
    map using the stated finite sum. The
    explicit function is only an existence
    witness; consumers use the opaque map's laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct SimplexCubeParametrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_parametrisation_exists]: the original
    map in the first display of
    4.1.27, p. 384, exists for every
    ordered vertex family, including degenerate
    vertices and the zero-dimensional source. *)
Theorem simplex_cube_parametrisation_exists (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  exists f:R_n R m->R_n R n,is_simplex_cube_parametrisation v f.
Proof.
exists (fun x=>v ord0+\sum_(i:'I_m)
  (simplex_cube_prefix_product x (val i).+1)*:simplex_consecutive_edge_family v i).
by move=>x.
Qed.
