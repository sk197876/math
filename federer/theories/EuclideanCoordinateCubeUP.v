(** Federer (1969), 3.2.38, pp. 274--275: independent coordinate
    laws for the compact cubes in the finite good/bad subdivision. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_coordinate_cube]: supporting specification
    of a compact cube of side h in Federer 3.2.38, p. 274.
    Its lower corner may have different coordinates. The carrier is
    specified before existence; h=0 and ambient dimension zero remain. *)
Definition is_euclidean_coordinate_cube (R:realType) n (a:R_n R n) (h:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  0<=h /\forall x,Q x <->forall i,a i<=x i<=a i+h.

(** Source for [euclidean_coordinate_cube_exists]: local existence
    from the independent coordinate laws for the cubes in Federer
    3.2.38, p. 274. No global chosen cube is introduced. *)
Lemma euclidean_coordinate_cube_exists (R:realType) n (a:R_n R n) (h:R):
  0<=h ->exists Q,is_euclidean_coordinate_cube a h Q.
Proof. move=>hh; exists [set x:inner_metric_space (@euclidean_inner_productP R n)|forall i,a i<=x i<=a i+h]; by split. Qed.
