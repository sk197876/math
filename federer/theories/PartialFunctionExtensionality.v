(** General set-theoretic background for Federer (1969),
    3.1.22, p. 235: a relative differential is determined
    by its values on exactly its tangent-cone domain. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [partial_function_graph_extensionality]: supporting
    uniqueness of Df(a) relative to S in Federer 3.1.22,
    p. 235. Equal single-valued graphs define equal partial
    functions; no outside-domain values are compared. *)
Lemma partial_function_graph_extensionality (X Y:Type) (f g:partial_function X Y) :
  (forall x y,partial_function_graph f x y <-> partial_function_graph g x y) -> f=g.
Proof.
case:f=>F hF; case:g=>G hG /=h.
have he:F=G.
  apply: funext=>x; apply: funext=>y.
  exact (boolp.propositional_extensionality (h x y)).
subst G.
have hh:hF=hG:=Prop_irrelevance _ _.
by rewrite hh.
Qed.
