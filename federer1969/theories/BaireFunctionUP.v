(** Federer (1969), 2.2.15, p. 70: Baire classes and the smallest such class
    containing all continuous maps. These are abstract closure and
    minimality laws, with existence proved separately. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import PointwiseLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_baire_class]: direct first definition
    in Federer 2.2.15, p. 70. The source is a
    set, the target is a metric space, and the family
    contains all pointwise limits of its sequences. *)
Definition is_baire_class (R : realType) (X : Type) (Y : metricType R)
    (F : set (X -> Y)) : Prop :=
  forall f g, (forall n : nat, F (f n)) -> is_pointwise_limit f g -> F g.

(** Source for [is_baire_function_family]: direct smallest-class
    specification for Baire functions in Federer 2.2.15,
    p. 70. The source now carries a topology; continuity
    is a generator and pointwise sequential closure is the law. *)
Record is_baire_function_family (R : realType) (X : topologicalType) (Y : metricType R)
    (F : set (X -> Y)) : Prop := {
  baire_family_closed : is_baire_class F;
  baire_family_continuous : forall f, continuous f -> F f;
  baire_family_least : forall G, is_baire_class G ->
    (forall f, continuous f -> G f) -> F `<=` G
}.
