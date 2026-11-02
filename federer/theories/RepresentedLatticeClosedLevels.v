(** Federer (1969), 2.5.3, p. 94: closed unit levels in the inner
    approximation and measurability criteria. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealIntegralFunctionalUP SummableRealFunctionUP DaniellLatticeMeasurable
  ExtendedRealOrderTopology MeasurableFunctionBorel CountableOrderIntervals TopologicalBorel MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_closed_upper_level_measurable]:
    measurability of {f>=b} supporting Federer 2.5.3, p. 94 Every lattice
    member is allowed, with no sign condition. *)
Lemma represented_lattice_closed_upper_level_measurable (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A) (f : X -> R) (b : R) :
  L f -> measure_measurable mu [set x | (b <= f x)%R].
Proof.
move=> hf; have hi := hA f hf.
rewrite -real_total_upper_level.
apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm _ hi.1).
apply: closed_borel_set; exact: order_closed_upper_ray_closed.
Qed.
