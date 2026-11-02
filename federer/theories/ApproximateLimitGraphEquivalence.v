(** Federer (1969), 3.1.3(4), p. 213: the translated section
    has the same graph in block coordinates. Approximate limits depend
    only on that graph, not on record proofs of single-valuedness. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionGraphEquivalence MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [approximate_limit_graph_equivalent]: supporting
    extensionality of the definition in Federer 2.9.12, p. 158,
    used in the block-coordinate identity of 3.1.3(4), p. 213. *)
Lemma approximate_limit_graph_equivalent (R : realType) (X : metricType R)
    (Y : topologicalType) (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f g : partial_function X Y) x y :
  (forall z v, partial_function_graph f z v <-> partial_function_graph g z v) ->
  is_measure_approximate_limit phi V f x y -> is_measure_approximate_limit phi V g x y.
Proof.
move=> he hf W hn; rewrite -(partial_function_equivalent_preimages he).
exact: @hf W hn.
Qed.
