(** Federer (1969), 2.3.2, p. 74: the paired function used to deduce
    numerical closure from (4)–(5). This is ordinary set-theoretic graph
    pairing, with no arbitrary values outside the common domain. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_function_pair]: supporting paired graph in Federer
    2.3.2, p. 74, numerical-operations paragraph *)
Definition partial_function_pair (X Y Z : Type)
    (f : partial_function X Y) (g : partial_function X Z) : partial_function X (Y * Z).
Proof.
refine (@Build_partial_function X (Y * Z)
  (fun x p => partial_function_graph f x p.1 /\ partial_function_graph g x p.2) _).
move=> x [a b] [c d] [ha hb] [hc hd] /=.
have -> : a = c := partial_function_single_valued ha hc.
have -> : b = d := partial_function_single_valued hb hd.
by [].
Defined.

(** Source for [partial_function_pair_domain]: direct common domain of the
    pair used for Federer 2.3.2, p. 74 *)
Lemma partial_function_pair_domain (X Y Z : Type)
    (f : partial_function X Y) (g : partial_function X Z) :
  partial_function_domain (partial_function_pair f g) =
  partial_function_domain f `&` partial_function_domain g.
Proof.
apply/seteqP; split=> x.
- move=> [[y z] [hy hz]]; split; [by exists y|by exists z].
- move=> [[y hy] [z hz]]; by exists (y,z).
Qed.

(** Source for [partial_function_pair_rectangle_preimage]:
    supporting rectangle inverse-image identity for Federer
    2.3.2(5), p. 73, applied to numerical operations on p. 74. *)
Lemma partial_function_pair_rectangle_preimage (X Y Z : Type)
    (f : partial_function X Y) (g : partial_function X Z) (A : set Y) (B : set Z) :
  partial_function_preimage (partial_function_pair f g) (A `*` B) =
  partial_function_preimage f A `&` partial_function_preimage g B.
Proof.
apply/seteqP; split=> x.
- move=> [[y z] [[hy hz] [ha hb]]]; split; [by exists y|by exists z].
- move=> [[y [hy ha]] [z [hz hb]]]; exists (y,z); by split; split.
Qed.
