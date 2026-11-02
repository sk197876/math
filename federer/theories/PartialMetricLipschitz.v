(** Federer (1969), 3.2.14(1), p. 251: a
    Lipschitzian parametrization may have a proper source domain.
    Express its actual graph without requiring an inhabited target
    or filling values outside the parametrizing set. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import PartialFunctionUP LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_function_range]: the image of the
    parametrizing function in Federer 3.2.14(1), p. 251.
    Only actual graph values belong to this image. *)
Definition partial_function_range (X Y:Type) (f:partial_function X Y):set Y:=
  [set y|exists x,partial_function_graph f x y].

(** Source for [is_partial_metric_lipschitz_bound]: the
    Lipschitzian function on its actual source set in Federer
    3.2.14(1), p. 251, specified by the distance inequality. *)
Definition is_partial_metric_lipschitz_bound (R:realType) (X Y:metricType R)
    (f:partial_function X Y) (L:R):Prop:=
  0<=L /\forall x y a b,partial_function_graph f x a ->partial_function_graph f y b ->
    mdist a b<=L*mdist x y.
