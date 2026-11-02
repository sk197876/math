(** Federer (1969), 2.4.12, p. 87: uniform finite-image approximation on a
    compact ball for the corrected p=infinity density assertion (erratum p.
    2, book p. 87 line 18). The abstract laws below express the needed
    finite approximation and preservation of a distinguished point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_finite_approximation]: supporting abstract finite
    Borel approximation for Federer 2.4.12, p. 87 The reference-point bound
    ensures that a prescribed zero is fixed, preserving countable
    measurability of the nonzero locus in the L-infinity application. *)
Record is_compact_finite_approximation (R : realType) (Y : metricType R)
    (K : set Y) (epsilon : R) (y0 : Y) (a : Y -> Y) : Prop := {
  (** Source for [compact_finite_borel]: Borel pieces in the
      finite partition used for Federer 2.4.12, p. 87. *)
  compact_finite_borel : is_borel_function a;
  (** Source for [compact_finite_image]: finite-image property
      required for density in Federer 2.4.12, p. 87. *)
  compact_finite_image : finite_set (a @` setT);
  (** Source for [compact_finite_reference_error]: supporting zero-
      preserving bound for Federer 2.4.12, p. 87. *)
  compact_finite_reference_error : forall x, mdist x (a x) <= mdist x y0;
  (** Source for [compact_finite_uniform_error]: Supporting Federer 2.4.12
    density assertion. *)
  compact_finite_uniform_error : forall x, K x -> mdist x (a x) < epsilon
}.
