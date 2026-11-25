(** Federer (1969), 2.2.14, p. 70: represent the graph as the inverse image
    of the diagonal under f times identity. The forward graph result below
    only needs a separable metric target; completeness is used for the
    subsequent Suslin-image result. Source context: BorelFunctionUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import TopologicalBorel BorelFunctionUP BorelFunctionBasic
  BorelProductMaps CountableOpenBaseUP SeparableMetricBaseSealed
  TopologicalProductMaps ContinuousClosedGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_function_graph]: supporting Borel graph for Federer
    2.2.14, p. 70. The set of (x,y) satisfying f(x)=y is the Borel preimage
    of the closed diagonal. *)
Theorem borel_function_graph (R : realType) (X : topologicalType) (Y : metricType R)
    (f : X -> Y) :
  (exists D : set Y, countable D /\ dense D) -> is_borel_function f ->
  borel_set [set p : X * Y | f p.1 = p.2].
Proof.
move=> [D [hc hd]] hf.
pose U := @SeparableMetricBase.value R Y D hc hd.
have hU : is_countable_open_base U := @SeparableMetricBase.laws R Y D hc hd.
pose F (p : X * Y) := (f p.1,p.2).
have hF : is_borel_function F.
  apply: (@borel_pair_function [the topologicalType of (X * Y)%type] Y Y
    (fun p => f p.1) (@snd X Y) U U hU hU).
  - exact: borel_function_composition (continuous_borel_function (@first_projection_continuous X Y)) hf.
  - exact: continuous_borel_function (@second_projection_continuous X Y).
have hdiag : closed [set p : Y * Y | p.1 = p.2].
  apply: (@continuous_map_closed_graph Y Y id); first exact: metric_hausdorff.
  by move=> y V hV.
exact: (@borel_function_preimage [the topologicalType of (X * Y)%type]
  [the topologicalType of (Y * Y)%type] F hF _ (closed_borel_set hdiag)).
Qed.
