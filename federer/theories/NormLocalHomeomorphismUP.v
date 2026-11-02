(** Federer (1969), 3.1.1, pp. 209–210: a function maps a
    neighbourhood of a homeomorphically onto a neighbourhood of f(a).
    Both neighbourhoods carry their actual subspace topologies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  MetricSubsetBackground HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_norm_local_homeomorphism]: the neighbourhood
    homeomorphism in Federer 3.1.1(1), p. 209, and the inverse-function
    conclusion on p. 210. The specification requires genuine
    homeomorphisms of norm-metric subspaces, not merely a bijection or
    formal inverse identities. Neighbourhoods need not themselves be open. *)
Definition is_norm_local_homeomorphism (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X) :=
  exists (U : set (real_norm_metric_space hNX))
         (V : set (real_norm_metric_space hNY)),
    norm_domain_interior NX U a /\ norm_domain_interior NY V (f a) /\
    (forall x, U x -> A x) /\
    exists F : metric_subset U -> metric_subset V,
      (forall x, val (F x) = f (val x)) /\ is_homeomorphism F.
