(** Federer (1969), 3.2.38, p. 274: the finite equal-side cube
    grid and its subsequent subdivision into v^m smaller cubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_cube_grid_indices]: finite Cartesian
    indexing of k^n equal cubes, supporting both subdivisions in
    Federer 3.2.38, p. 274. The n=0 family has one member. *)
Definition coordinate_cube_grid_indices n k:finType:=
  [the finType of {ffun 'I_n->'I_k}].

(** Source for [is_equal_coordinate_cube_grid]: independent coordinate
    laws for equal closed cubes of side h, Federer 3.2.38, p. 274.
    Covering, compactness, overlap nullity and volume are conclusions
    rather than assumed fields. Arbitrary positive natural k is used. *)
Definition is_equal_coordinate_cube_grid (R:realType) n k (a:R_n R n) (h:R)
    (Q:coordinate_cube_grid_indices n k->
      set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  (0<k)%N /\0<=h /\forall s x,Q s x <->forall i,
    a i+(s i)%:R*h<=x i<=a i+((s i).+1)%:R*h.

Arguments is_equal_coordinate_cube_grid {R n} k a h Q.

(** Source for [equal_coordinate_cube_grid_exists]: local finite-grid
    existence for the cube subdivision in Federer 3.2.38, p. 274.
    The witness serves only to prove the independent laws; no global
    grid or coordinate rounding function is selected. *)
Lemma equal_coordinate_cube_grid_exists (R:realType) n k (a:R_n R n) (h:R):
  (0<k)%N ->0<=h ->exists Q,is_equal_coordinate_cube_grid k a h Q.
Proof.
move=>hk hh.
exists (fun s:coordinate_cube_grid_indices n k=>[set x:inner_metric_space (@euclidean_inner_productP R n)|forall i,a i+(s i)%:R*h<=x i<=a i+((s i).+1)%:R*h]).
by split=>//; split.
Qed.
