(** Federer (1969), 2.10.44, printed p. 202: specify f on the three
    displayed source points by exactly the three printed target values.
    Nonexpansion, its optimal constant and failure of extension are derived
    later, not assumed. Values outside the original three-point source are
    irrelevant. Source context and coordinates: KirszbraunCorners.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import EuclideanInnerProduct InnerMetric PlaneSupremumNorm KirszbraunCorners.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_kirszbraun_corner_map]: direct three
    prescribed values of f in 2.10.44, p. 202.
    This specifies only the original finite graph;
    no Lipschitz or nonextension claim is a field. *)
Record is_kirszbraun_corner_map (R : realType)
    (f : plane_supremum_metric R -> inner_metric_space (@euclidean_inner_productP R 2)) : Prop := {
  (** Source for [kirszbraun_corner_map_first_law]: direct
      f(1,-1)=(1,0) in 2.10.44, p. 202. *)
  kirszbraun_corner_map_first_law : f (kirszbraun_corner_first R)=kirszbraun_equilateral_first R;
  (** Source for [kirszbraun_corner_map_second_law]: direct
      f(-1,1)=(-1,0) in 2.10.44, p. 202. *)
  kirszbraun_corner_map_second_law : f (kirszbraun_corner_second R)=kirszbraun_equilateral_second R;
  (** Source for [kirszbraun_corner_map_third_law]: direct
      f(1,1)=(0,sqrt(3)) in 2.10.44, p. 202. *)
  kirszbraun_corner_map_third_law : f (kirszbraun_corner_third R)=kirszbraun_equilateral_third R
}.
