(** Federer (1969), 3.2.14, p. 252: the closure
    of an m rectifiable set is m rectifiable. Specify
    the supporting graph closure independently of its
    existence construction. No complete target is assumed. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_partial_lipschitz_graph_closure]: the
    graph extension supporting the closure assertion of
    Federer 3.2.14, p. 252. The extended graph is precisely
    the closure of the original graph in the product topology;
    it need not be defined at every limit source point. *)
Definition is_partial_lipschitz_graph_closure (R : realType)
    (X Y : metricType R) (f g : partial_function X Y) : Prop :=
  forall x y, partial_function_graph g x y <->
    closure [set p : X * Y | partial_function_graph f p.1 p.2] (x,y).
