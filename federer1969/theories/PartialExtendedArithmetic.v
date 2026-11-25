(** Federer (1969), 2.3.2, p. 74: pointwise partial extended-real
    arithmetic, with undefined pairs exactly as in 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition
  PartialFunctionBinaryOperation ExtendedRealOrderTopology ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_function_add]: direct pointwise
    sum in Federer 2.3.2, p. 74, with opposite infinities
    excluded as required by 2.1.1, p. 51. *)
Definition partial_extended_function_add (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :=
  partial_function_binary_on f g [set p | adde_def p.1 p.2]
    (fun p => (p.1 + p.2 : extended_real_line R)).

(** Source for [partial_extended_function_multiply]: direct pointwise
    product in Federer 2.3.2, p. 74. The ordinary partial
    product excludes zero times infinity; the separate zero-product
    convention of 2.1.1 is not substituted here. *)
Definition partial_extended_function_multiply (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :=
  partial_function_binary_on f g [set p | mule_def p.1 p.2]
    (fun p => (p.1 * p.2 : extended_real_line R)).

(** Source for [partial_extended_function_subtract]: direct pointwise
    difference in Federer 2.3.2, p. 74, defined as addition
    of the negative with the partial convention of 2.1.1, p. 51. *)
Definition partial_extended_function_subtract (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :=
  partial_extended_function_add f (partial_function_postcompose g
    (fun y => (-y : extended_real_line R))).

(** Source for [partial_extended_function_add_graph]: supporting
    exact link between the pointwise sum in Federer 2.3.2,
    p. 74, and the partial scalar operation of 2.1.1, p. 51. *)
Lemma partial_extended_function_add_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_extended_function_add f g) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ extended_add a b = Some z.
Proof.
split.
- move=> [[a b] [[ha hb] [hd he]]]; exists a, b; split=> //; split=> //.
  by rewrite /extended_add hd he.
- move=> [a [b [ha [hb he]]]]; rewrite /extended_add in he.
  case hd : (adde_def a b) in he=> //; have hz : a+b = z by case: he.
  exists (a,b); by split; [split|split].
Qed.

(** Source for [partial_extended_function_multiply_graph]: supporting
    exact link between the pointwise product in Federer 2.3.2,
    p. 74, and its undefined scalar cases in 2.1.1, p. 51. *)
Lemma partial_extended_function_multiply_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_extended_function_multiply f g) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ extended_multiply a b = Some z.
Proof.
split.
- move=> [[a b] [[ha hb] [hd he]]]; exists a, b; split=> //; split=> //.
  by rewrite /extended_multiply hd he.
- move=> [a [b [ha [hb he]]]]; rewrite /extended_multiply in he.
  case hd : (mule_def a b) in he=> //; have hz : a*b = z by case: he.
  exists (a,b); by split; [split|split].
Qed.
