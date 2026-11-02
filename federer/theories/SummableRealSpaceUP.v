(** Federer (1969), 2.6.4, pp. 118–119: the vector spaces of total-domain
    summable real functions in the tensor diagram. Erratum p. 2, book p. 119
    lines 3, 4, 6, requires the total-domain notation. We keep literal
    functions, not classes modulo null functions. The subspace laws follow
    from 2.4.4(3)–(4), p. 82. his Chapter 18 does not state this tensor
    diagram. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal.
From Federer Require Import SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_summable_real_space]: abstract total-domain
    L1 carrier in Federer 2.6.4, pp. 118–119, with
    erratum p. 2, book p. 119 lines 3, 4, 6.
    A linear evaluation identifies the carrier precisely with all
    summable functions; it is injective on literal functions. *)
Definition is_summable_real_space (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (V : lmodType R) (value : {linear V -> (X -> R^o)}) :=
  injective value /\ forall f, summable_real_functions mu f <-> exists v, value v=f.
