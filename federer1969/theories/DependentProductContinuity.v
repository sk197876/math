(** General topology supporting Federer (1969), 2.6.6, p. 120: a map into a
    product is continuous when all its coordinate maps are continuous.
    Source context and the supporting countable-product correspondence. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [dependent_product_map_continuous]: supporting universal
    property of the product topology for p_a and its sections in
    Federer 2.6.6, p. 120. The index set is arbitrary. *)
Lemma dependent_product_map_continuous (T : topologicalType) (I : choiceType)
    (Y : I -> topologicalType) (f : T -> prod_topology Y) :
  (forall i, continuous (fun x=>f x i)) -> continuous f.
Proof.
move=> hf x.
have hF : Filter (f @ nbhs x) := @fmap_filter T (prod_topology Y) f (nbhs x) (nbhs_filter x).
apply/(product_topology_cvg _ hF)=> i; exact: hf i x.
Qed.
