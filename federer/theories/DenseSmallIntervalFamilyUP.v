(** Federer (1969), 3.2.33, p. 270: independent
    laws for the open intervals U_j with dense union in (0,1)
    and a positive-length omitted set. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground RealOpenIntervals LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_dense_small_interval_family]: the choice of
    U_j and V in Federer 3.2.33, p. 270. Each interval
    is nonempty and lies in (0,1). Its length is at most
    one half, a convenient normalization for the printed smooth
    series. Every open set meeting (0,1) meets the union, while
    the complement in (0,1) has positive Lebesgue length.
    These laws precede the existence proof and select no family. *)
Record is_dense_small_interval_family (R:realType) (a b:nat->R):Prop:={
  (** Source for [dense_small_interval_endpoints]: nonempty bounded
      subintervals of T, Federer 3.2.33, p. 270. *)
  dense_small_interval_endpoints:forall j,0<a j /\a j<b j /\b j<1;
  (** Source for [dense_small_interval_length]: supporting uniform
      half-length bound for the series in Federer 3.2.33, p. 270. *)
  dense_small_interval_length:forall j,b j-a j<= 1/2;
  (** Source for [dense_small_interval_hits]: V is dense in T,
      Federer 3.2.33, p. 270, expressed by actual open intersections. *)
  dense_small_interval_hits:forall U:set (real_line_metric R),open U ->
    (exists x,real_open_interval 0 1 x /\U x) ->
    exists x,U x /\(\bigcup_j real_open_interval (a j) (b j)) x;
  (** Source for [dense_small_interval_positive_complement]: positive
      length of T minus V in Federer 3.2.33, p. 270. *)
  dense_small_interval_positive_complement:(0<lebesgue_scalar_measure
    (real_open_interval 0 1 `\` (\bigcup_j real_open_interval (a j) (b j))))%E
}.
