(** Federer (1969), 2.6.2(4), p. 115: fix one coordinate of a partial
    integrand. The section domain is exactly the corresponding section of
    its original domain; no values are filled in. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionPrecomposition ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_product_vertical_section]: direct
    function y mapped to f(x,y) in Federer 2.6.2(4),
    p. 115, on its exact partial domain. *)
Definition partial_product_vertical_section (X Y Z : Type) (f : partial_function (X * Y) Z) x :=
  partial_function_precompose (fun y => (x,y)) f.

(** Source for [partial_product_horizontal_section]: direct
    function x mapped to f(x,y) in Federer 2.6.2(4),
    p. 115, on its exact partial domain. *)
Definition partial_product_horizontal_section (X Y Z : Type) (f : partial_function (X * Y) Z) y :=
  partial_function_precompose (fun x => (x,y)) f.

(** Source for [partial_product_vertical_agreement]: supporting
    agreement-set identity for the null modifications in the
    function step of Federer 2.6.2, p. 117. *)
Lemma partial_product_vertical_agreement (X Y Z : Type)
    (f g : partial_function (X * Y) Z) x :
  partial_function_agreement (partial_product_vertical_section f x) (partial_product_vertical_section g x) =
    product_vertical_section (partial_function_agreement f g) x.
Proof. by []. Qed.
