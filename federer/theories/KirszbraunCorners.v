(** Federer (1969), 2.10.44, printed p. 202: the three source corners
    (1,-1), (-1,1), (1,1) and target points (1,0), (-1,0), (0,sqrt(3)). Use
    the existing public Cartesian pairing to state these explicit coordinate
    witnesses. The source carries the opaque coordinate-supremum norm; the
    target keeps the usual Euclidean metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanRealPlane
  PlaneSupremumNorm PlanePairNormGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_corner_first]: direct source
    point (1,-1) in 2.10.44, p. 202. *)
Definition kirszbraun_corner_first (R : realType) : plane_supremum_metric R := euclidean_real_plane_pair 1 (-1).
(** Source for [kirszbraun_corner_second]: direct source
    point (-1,1) in 2.10.44, p. 202. *)
Definition kirszbraun_corner_second (R : realType) : plane_supremum_metric R := euclidean_real_plane_pair (-1) 1.
(** Source for [kirszbraun_corner_third]: direct source
    point (1,1) in 2.10.44, p. 202. *)
Definition kirszbraun_corner_third (R : realType) : plane_supremum_metric R := euclidean_real_plane_pair 1 1.
(** Source for [kirszbraun_equilateral_first]: direct target
    value (1,0) in 2.10.44, p. 202. *)
Definition kirszbraun_equilateral_first (R : realType) :
    inner_metric_space (@euclidean_inner_productP R 2) := euclidean_real_plane_pair 1 0.
(** Source for [kirszbraun_equilateral_second]: direct target
    value (-1,0) in 2.10.44, p. 202. *)
Definition kirszbraun_equilateral_second (R : realType) :
    inner_metric_space (@euclidean_inner_productP R 2) := euclidean_real_plane_pair (-1) 0.
(** Source for [kirszbraun_equilateral_third]: direct target
    value (0,sqrt(3)) in 2.10.44, p. 202. *)
Definition kirszbraun_equilateral_third (R : realType) :
    inner_metric_space (@euclidean_inner_productP R 2) := euclidean_real_plane_pair 0 (Num.sqrt 3).

(** Source for [kirszbraun_corner_source]: direct three-
    point original source S in 2.10.44, p. 202. *)
Definition kirszbraun_corner_source (R : realType) : set (plane_supremum_metric R) :=
  [set kirszbraun_corner_first R] `|` [set kirszbraun_corner_second R] `|` [set kirszbraun_corner_third R].

(** Source for [kirszbraun_corners_distinct]: supporting
    distinctness of the three printed source points
    in 2.10.44, p. 202. The orientation of
    the inequalities supports the private finite-map witness. *)
Lemma kirszbraun_corners_distinct (R : realType) :
  kirszbraun_corner_second R!=kirszbraun_corner_first R /\
  kirszbraun_corner_third R!=kirszbraun_corner_first R /\
  kirszbraun_corner_third R!=kirszbraun_corner_second R.
Proof.
split.
- apply/eqP=> he; have hh := congr1 (fun p : plane_supremum_metric R=>p ord0) he.
  rewrite /kirszbraun_corner_first /kirszbraun_corner_second !real_plane_pair_first_coordinate in hh; clear he; lra.
- split.
  + apply/eqP=> he; have hh := congr1 (fun p : plane_supremum_metric R=>p ord_max) he.
    rewrite /kirszbraun_corner_first /kirszbraun_corner_third !real_plane_pair_second_coordinate in hh; clear he; lra.
  + apply/eqP=> he; have hh := congr1 (fun p : plane_supremum_metric R=>p ord0) he.
    rewrite /kirszbraun_corner_second /kirszbraun_corner_third !real_plane_pair_first_coordinate in hh; clear he; lra.
Qed.

(** Source for [kirszbraun_corner_members]: supporting
    membership of the three displayed points in
    the source of 2.10.44, p. 202. *)
Lemma kirszbraun_corner_members (R : realType) :
  kirszbraun_corner_source (kirszbraun_corner_first R) /\
  kirszbraun_corner_source (kirszbraun_corner_second R) /\
  kirszbraun_corner_source (kirszbraun_corner_third R).
Proof.
split; first by left; left.
split; [by left; right|by right].
Qed.
