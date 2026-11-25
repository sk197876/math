(** Federer (1969), 3.2.2, p. 242: a univalent map
    restricted to E has an inverse with exactly f(E) as its
    domain. This general set-theoretic existence proof never
    assigns inverse values outside that image. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [restricted_inverse_graph_exists]: the inverse
    (f restricted to E)^{-1} in Federer 3.2.2, p. 242.
    Specify its exact graph by reversing the restricted graph;
    its being a partial function follows from univalence. *)
Theorem restricted_inverse_graph_exists (X Y:Type) (E:set X) (f:X->Y):
  {in E &,injective f} -> exists g:partial_function Y X,
    forall y x,partial_function_graph g y x <-> E x /\ f x=y.
Proof.
move=>hf.
have hu y x z:(E x /\ f x=y) -> (E z /\ f z=y) -> x=z.
  move=>[hx hfx] [hz hfz]; apply:(hf x z (mem_set hx) (mem_set hz)).
  by rewrite hfx hfz.
exists (@Build_partial_function Y X (fun y x=>E x /\ f x=y) hu); by move=>y x.
Qed.
