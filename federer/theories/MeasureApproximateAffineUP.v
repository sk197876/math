(** Federer (1969), 3.2.16, p. 253:
    the affine-remainder criterion for approximate
    differentiability, stated independently of its
    equivalence proof and any selected shell radii. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP MeasureRestriction MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_affine_approximation_set]:
    the set {x:|f(x)-eta-D(x-a)|<=e|x-a|}
    in Federer 3.2.16, p. 253. Only
    actual graph values of f enter this set. *)
Definition measure_affine_approximation_set (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (f : partial_function X Y) (a : X) (eta : Y) (D : Hom X Y) (e : R) : set X :=
  [set x | exists y, partial_function_graph f x y /\
    NY (y-eta-D (x-a))<=e*NX (x-a)].

(** Source for [has_measure_approximate_affine_criterion]:
    existence of a continuous linear affine
    approximation and all zero-density error tests,
    Federer 3.2.16, p. 253. Eta need
    not be a value of f at the base point. *)
Definition has_measure_approximate_affine_criterion (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) (a : X) (eta : Y) (D : Hom X Y) : Prop :=
  norm_bounded_linear NX NY D /\ forall e : R, 0<e ->
    partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
      (measure_restrict phi (~` measure_affine_approximation_set NX NY f a eta D e))) a 0%E.
