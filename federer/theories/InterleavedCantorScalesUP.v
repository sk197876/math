(** Federer (1969), 2.10.29, p. 194: abstract laws of the interleaved
    subdivision schedules, interval lengths and spacings used in the product
    counterexample. Use the split laws of 2.10.28(4), p. 192; the explicit
    power formulas are later consequences. Do not assume the desired
    interleaving or convergence. Federer's erratum p. 4, book p. 194 line 8,
    corrects the last term of the displayed interleaving to
    sigma_j>=t_(j+1)->0. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import CantorSplitRadiusUP CantorSplitRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [interleaved_cantor_scale_data]: supporting
    data of the six scalar sequences in
    2.10.29, p. 194, before specifying
    laws or selecting an implementation. Widths
    at j represent the printed s_j,sigma_j;
    subdivisions and spacings at j represent
    the printed n_(j+1),nu_(j+1),t_(j+1),tau_(j+1). *)
Record interleaved_cantor_scale_data (R : realType) := {
  (** Source for [cantor_left_subdivision]: direct
      first-factor subdivision numbers in
      2.10.29, p. 194, with zero-based schedule. *)
  cantor_left_subdivision : nat -> nat;
  (** Source for [cantor_right_subdivision]: direct
      second-factor subdivision numbers in
      2.10.29, p. 194, with zero-based schedule. *)
  cantor_right_subdivision : nat -> nat;
  (** Source for [cantor_left_width]: direct
      first-factor interval lengths s_j in
      2.10.29, p. 194. *)
  cantor_left_width : nat -> R;
  (** Source for [cantor_right_width]: direct
      second-factor interval lengths sigma_j in
      2.10.29, p. 194. *)
  cantor_right_width : nat -> R;
  (** Source for [cantor_left_spacing]: direct
      first-factor t_(j+1) in 2.10.29,
      p. 194, with zero-based spacing index. *)
  cantor_left_spacing : nat -> R;
  (** Source for [cantor_right_spacing]: direct
      second-factor tau_(j+1) in 2.10.29,
      p. 194, with zero-based spacing index. *)
  cantor_right_spacing : nat -> R
}.

(** Source for [is_interleaved_cantor_scales]: direct
    subdivision and spacing choice laws in
    2.10.29, p. 194. State equal-cost
    lengths axiomatically through the already
    specified split radius. For a power gauge
    their explicit formulas follow from
    power_cantor_split_length. Interleaving,
    shrinking mesh and product measure claims
    are not defining assumptions. *)
Record is_interleaved_cantor_scales (R : realType) (h : R -> R)
    (D : interleaved_cantor_scale_data R) : Prop := {
  (** Source for [interleaved_cantor_left_root]: direct
      s_0=1 in 2.10.29, p. 194. *)
  interleaved_cantor_left_root : cantor_left_width D 0%N = 1;
  (** Source for [interleaved_cantor_right_root]: direct
      sigma_0=1 in 2.10.29, p. 194. *)
  interleaved_cantor_right_root : cantor_right_width D 0%N = 1;
  (** Source for [interleaved_cantor_left_count]: direct
      n_j>=2 in 2.10.29, p. 194. *)
  interleaved_cantor_left_count : forall j, (2<=cantor_left_subdivision D j)%N;
  (** Source for [interleaved_cantor_right_count]: direct
      nu_j>=2 in 2.10.29, p. 194. *)
  interleaved_cantor_right_count : forall j, (2<=cantor_right_subdivision D j)%N;
  (** Source for [interleaved_cantor_left_split]: direct
      first-factor equal-cost child length of
      2.10.29, p. 194, via 2.10.28(4). *)
  interleaved_cantor_left_split : forall j,
    is_cantor_split_radius h (cantor_left_width D j)
      (cantor_left_subdivision D j) (cantor_left_width D j.+1);
  (** Source for [interleaved_cantor_right_split]: direct
      second-factor equal-cost child length of
      2.10.29, p. 194, via 2.10.28(4). *)
  interleaved_cantor_right_split : forall j,
    is_cantor_split_radius h (cantor_right_width D j)
      (cantor_right_subdivision D j) (cantor_right_width D j.+1);
  (** Source for [interleaved_cantor_left_spacing_law]: direct
      t_j=(s_(j-1)-s_j)/(n_j-1) in
      2.10.29, p. 194. *)
  interleaved_cantor_left_spacing_law : forall j,
    cantor_left_spacing D j=cantor_split_spacing (cantor_left_width D j)
      (cantor_left_subdivision D j) (cantor_left_width D j.+1);
  (** Source for [interleaved_cantor_right_spacing_law]: direct
      tau_j=(sigma_(j-1)-sigma_j)/(nu_j-1)
      in 2.10.29, p. 194. *)
  interleaved_cantor_right_spacing_law : forall j,
    cantor_right_spacing D j=cantor_split_spacing (cantor_right_width D j)
      (cantor_right_subdivision D j) (cantor_right_width D j.+1);
  (** Source for [interleaved_cantor_left_small_spacing]: direct
      t_j<=sigma_(j-1)^j in 2.10.29,
      p. 194, before selecting the second split. *)
  interleaved_cantor_left_small_spacing : forall j,
    cantor_left_spacing D j<=(cantor_right_width D j)^+j.+1;
  (** Source for [interleaved_cantor_right_small_spacing]: direct
      tau_j<=s_j^j in 2.10.29, p. 194,
      after the first split is fixed. *)
  interleaved_cantor_right_small_spacing : forall j,
    cantor_right_spacing D j<=(cantor_left_width D j.+1)^+j.+1
}.
