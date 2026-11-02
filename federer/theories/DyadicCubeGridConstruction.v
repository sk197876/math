(** Private existence witness for the cube families of Federer (1969),
    2.10.47, p. 204. Coordinate inequalities implement the abstract carrier
    law. The witness is hidden by opaque module ascription; geometry
    downstream uses only that law. Source context: DyadicCubeGridUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric DyadicCubeGridUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dyadic_cube_grid_exists]: proved existence
    of the nested-grid carriers used in 2.10.47,
    p. 204. Subdivision properties are consequences of
    these carrier laws and are proved separately. *)
Theorem dyadic_cube_grid_exists (R : realType) n (a : R_n R n) :
  exists Q, is_dyadic_cube_grid a Q.
Proof.
exists (fun j (s : dyadic_cube_indices n j)=>
  [set x : inner_metric_space (@euclidean_inner_productP R n) | forall i,
    a i+(s i)%:R/((2^j)%N)%:R<=x i<=a i+((s i).+1)%:R/((2^j)%N)%:R]).
by move=> j s x.
Qed.
