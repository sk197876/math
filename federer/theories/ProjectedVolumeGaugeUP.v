(** Federer (1969), 2.10.4, p. 172, initial display: take the supremum of
    L^m[p(S)] over p in O*(n,m). Here L^m is the actual Euclidean Lebesgue
    measure from 2.6.5, pp. 119–120, and O* is the Chapter 1
    adjoint-of-isometry family. Specify the extended-real supremum before
    selecting its value. The target assumes 0<m<=n. Supporting interfaces
    also permit m=0 with the existing empty-product Lebesgue convention. No
    relevant entry occurs in the local LaTeX erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  CoordinateProjection EuclideanLebesgueDimensions ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [projected_volume_values]: direct value
    family in Federer 2.10.4, p. 172. Projection
    images may be arbitrary sets: the given Lebesgue
    outer measure is defined on all sets. *)
Definition projected_volume_values (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) : set (\bar R) :=
  [set v | exists p : {linear R_n R n -> R_n R m},
    O_star p /\ v=euclidean_lebesgue_measure m (p @` A)].

(** Source for [is_projected_volume_gauge]: abstract
    least-upper-bound laws for the first display in
    Federer 2.10.4, p. 172. Both finite and
    infinite projected volumes are retained. *)
Definition is_projected_volume_gauge (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (c : \bar R) :=
  is_extended_real_supremum (projected_volume_values m A) c.
