(** Federer (1969), 2.4.10, p. 85, final paragraph: the interval integral
    uses the half-open set a<x<=b, with extended endpoints, for X equal to
    the real or extended-real line. A coordinate map supplies one common
    supporting statement for both ambient types; their direct
    specialisations are defined below. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_half_open_interval]: supporting common
    set notation for the half-open interval in Federer
    2.4.10, p. 85. The coordinate is inclusion
    of reals or identity on extended reals in the printed cases. *)
Definition measure_half_open_interval (R : realType) (X : Type)
    (coordinate : X -> \bar R) (a b : \bar R) := [set x | a < coordinate x <= b].

(** Source for [is_measure_interval_integral]: abstract integral
    value over the half-open interval in Federer 2.4.10,
    p. 85, in a common coordinate-based formulation. *)
Definition is_measure_interval_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (coordinate : X -> \bar R) (a b : \bar R)
    (f : partial_function X (extended_real_line R)) z :=
  is_measure_subset_integral mu (measure_half_open_interval coordinate a b) f z.

(** Source for [is_measure_real_interval_integral]: direct
    real ambient-space abbreviation of Federer 2.4.10,
    p. 85, with both endpoints allowed to be infinite. *)
Definition is_measure_real_interval_integral (R : realType) (mu : set R -> \bar R)
    (a b : \bar R) (f : partial_function R (extended_real_line R)) z :=
  is_measure_interval_integral mu (fun x : R => x%:E) a b f z.

(** Source for [is_measure_extended_interval_integral]: direct
    extended-real ambient-space abbreviation of Federer 2.4.10,
    p. 85; the lower endpoint remains excluded. *)
Definition is_measure_extended_interval_integral (R : realType) (mu : set (\bar R) -> \bar R)
    (a b : \bar R) (f : partial_function (\bar R) (extended_real_line R)) z :=
  is_measure_interval_integral mu (fun x : \bar R => x) a b f z.
