(** Federer (1969), 3.2.16, pp. 252–253:
    approximate tangent directions and their directional
    cone tests. Definitions use arbitrary subsets and
    the supplied norm laws; neither a chosen geometric
    construction nor completeness is built into them. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureRestriction
  PartialFunctionUP MetricDensities TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_tangent_cone]: the
    first display of Federer 3.2.16, p. 252.
    Intersect Tan(S,a) over all subsets S whose
    complement has zero m-density under phi. The
    numbered item's claims assume m positive and phi
    a measure; neither measurability of S nor finite
    dimension is part of this definition. *)
Definition measure_approximate_tangent_cone (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    (phi : set X -> \bar R) m (a : X) : set X :=
  [set v | forall S : set X,
    partial_function_graph (@metric_density R (real_norm_metric_space hNX)
      m (measure_restrict phi (~` S))) a 0%E ->
    norm_tangent_cone NX S a v].

(** Source for [approximate_direction_cone]: E(a,v,e)
    in the second display of Federer 3.2.16,
    p. 252: some positive dilation of x-a
    lies within e of v. The source point a
    is not silently removed. *)
Definition approximate_direction_cone (R : realType)
    (X : lmodType R) (NX : X -> R) (a v : X) (e : R) : set X :=
  [set x | exists r : R, 0<r /\ NX (r *: (x-a)-v)<e].

(** Source for [positive_directional_hull]: the set
    T={a+r v:r>0,v in C} in Federer
    3.2.16, p. 253, first paragraph. No
    measurability or compactness is assumed by the
    definition; compactness of C is a theorem premise. *)
Definition positive_directional_hull (R : realType)
    (X : lmodType R) (a : X) (C : set X) : set X :=
  [set x | exists (r : R) (v : X), 0<r /\ C v /\ x=a+r *: v].
