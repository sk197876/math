(** Federer (1969), 2.3.2, p. 74: numerical binary operations on their
    actual domains. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_binary_on]: supporting graph
    definition of a binary operation with its given domain D in
    Federer 2.3.2, p. 74. No value is assigned to an
    undefined operation or outside either input domain. *)
Definition partial_function_binary_on (X Y Z W : Type)
    (f : partial_function X Y) (g : partial_function X Z) (D : set (Y * Z))
    (h : Y * Z -> W) : partial_function X W.
Proof.
refine (@Build_partial_function X W (fun x w => exists p,
  partial_function_graph (partial_function_pair f g) x p /\ D p /\ h p = w) _).
move=> x w v [p [hp [_ <-]]] [q [hq [_ <-]]].
by rewrite (partial_function_single_valued hp hq).
Defined.

(** Source for [partial_function_binary_on_domain]: exact domain
    qualification for the arithmetic assertions in Federer 2.3.2, p. 74 *)
Lemma partial_function_binary_on_domain (X Y Z W : Type)
    (f : partial_function X Y) (g : partial_function X Z) (D : set (Y * Z))
    (h : Y * Z -> W) : partial_function_domain (partial_function_binary_on f g D h) =
    partial_function_preimage (partial_function_pair f g) D.
Proof.
apply/seteqP; split=> x.
- move=> [w [p [hp [hd _]]]]; by exists p.
- move=> [p [hp hd]]; exists (h p); exists p; by split.
Qed.
