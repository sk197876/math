(** Federer (1969), 3.2.16, p. 253:
    approximate differentiability for an arbitrary
    measure and positive integer m. The actual
    partial domain of f is retained. Specifications
    precede existence and the opaque choice of its
    differential on the approximate tangent cone. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureRestriction MetricDensities MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_measure_approximate_differential]:
    the differentiable representative g on a
    neighbourhood U in Federer 3.2.16, p. 253.
    The complement of the actual agreement set
    has zero m-density. No value of f at a
    or outside its domain is required by the definition. *)
Definition has_measure_approximate_differential (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) (a : X) (D : Hom X Y) : Prop :=
  exists (U : set X) (g : X -> Y),
    has_norm_differential NX NY U g a D /\
    partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
      (measure_restrict phi (~` partial_function_agreement f
        (partial_function_source_restrict U (partial_function_total g))))) a 0%E.

(** Source for [measure_approximately_differentiable_at]:
    existence of a differentiable representative in
    Federer 3.2.16, p. 253. The standing
    norm and measure hypotheses remain explicit
    premises in the characterizing theorems. *)
Definition measure_approximately_differentiable_at (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) (a : X) : Prop :=
  exists D, has_measure_approximate_differential NY hNX phi m f a D.

(** Source for [is_measure_approximate_differential]:
    the restriction Dg(a) to Tan_m(phi,a),
    denoted (phi,m) ap Df(a) in Federer
    3.2.16, p. 253. An actual approximate
    differential witness is required; the exact
    graph is specified independently of its construction. *)
Definition is_measure_approximate_differential (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (phi : set X -> \bar R) m
    (f : partial_function X Y) (a : X) (d : partial_function X Y) : Prop :=
  measure_approximately_differentiable_at NY hNX phi m f a /\
  forall v y, partial_function_graph d v y <->
    measure_approximate_tangent_cone hNX phi m a v /\
    exists D, has_measure_approximate_differential NY hNX phi m f a D /\ D v=y.
