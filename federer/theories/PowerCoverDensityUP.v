(** Federer (1969), 2.10.29, p. 195: the higher Cartesian-power conclusion
    follows by multiplying small local power-density estimates. This
    supporting predicate records exactly those local bounds, before deriving
    a product law. It does not postulate the measure or the desired infinite
    covering-measure conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_vanishing_power_cover_density]: supporting
    local estimate used to iterate the product
    argument of 2.10.29, pp. 194–195.
    The finite bound d on diameter, including
    d=0, is explicit. No test-set measurability
    is required. *)
Definition is_vanishing_power_cover_density (R : realType) (X : metricType R)
    (p : R) (nu : set X -> \bar R) :=
  forall e : R, (0<e)%R -> exists delta : R, (0<delta)%R /\
    forall (S : set X) (d : R), (0<=d)%R -> (d<=delta)%R ->
      extended_metric_diameter S<=d%:E -> nu S<=(e*real_power d p)%R%:E.
