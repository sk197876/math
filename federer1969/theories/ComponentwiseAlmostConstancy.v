(** Federer (1969), 4.1.26, p. 384:
    a connected set disjoint from the boundary
    image lies in one complementary component.
    Componentwise almost constancy therefore gives
    almost constancy on that set. The set
    need not be open or measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [componentwise_almost_constant_on_connected_set]:
    the first connected-image conclusion of
    4.1.26, p. 384, after componentwise constancy.
    Empty sets are handled without choosing a
    point; outer-measure nullness handles arbitrary
    connected subsets, including nonmeasurable ones. *)
Theorem componentwise_almost_constant_on_connected_set
    (R:realType) (X:topologicalType) (mu:set X->\bar R)
    (hMu:is_measure mu) (W S:set X) (d:partial_function X R):
  connected S->S `<=` W->
  (forall a,W a->exists c:R,measure_almost_everywhere_on mu
    (connected_component W a) [set x|partial_function_graph d x c])->
  exists c:R,measure_almost_everywhere_on mu S [set x|partial_function_graph d x c].
Proof.
move=>hConnected hSW hComponents.
case:(pselect (exists a,S a))=>[[a ha]|hEmpty].
- have hSC:S `<=` connected_component W a.
    exact:(@connected_component_max X W S a ha hSW hConnected).
  have[c hC]:=hComponents a (hSW a ha);exists c.
  apply:(@measure_null_subset R X mu hMu _ _ _ hC).
  by move=>x [hx hNot];split;[exact:hSC x hx|exact:hNot].
- exists 0;rewrite /measure_almost_everywhere_on.
  have hZero:S `\` [set x|partial_function_graph d x 0]=set0.
    apply/seteqP;split;last by [].
    move=>x [hx _];exfalso;apply:hEmpty;by exists x.
  by rewrite hZero (measure_empty hMu).
Qed.
