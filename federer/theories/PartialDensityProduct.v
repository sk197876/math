(** Federer (1969), 2.4.10, p. 85: the product fg in the change-of-density
    identity uses the convention zero times infinity equals zero, from
    2.1.1, p. 51. We distinguish this product from the ordinary partial
    product of 2.3.2, which excludes zero-infinity pairs. Domains must still
    be common to both functions. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBinaryOperation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_density_product]: the pointwise product in Federer
    2.4.10, p. 85, with the zero- infinity convention explicit. *)
Definition partial_density_product (R : realType) (X : Type)
    (f h : partial_function X (extended_real_line R)) :=
  partial_function_binary_on f h setT
    (fun p => (extended_zero_product p.1 p.2 : extended_real_line R)).

(** Source for [partial_density_product_graph]: supporting graph
    law of the density product in Federer 2.4.10,
    p. 85, retaining the common domain even when one
    value is zero. *)
Lemma partial_density_product_graph (R : realType) (X : Type)
    (f h : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_density_product f h) x z <->
  exists a b, partial_function_graph f x a /\ partial_function_graph h x b /\ a*b=z.
Proof.
split.
- move=> [[a b] [[ha hb] [_ he]]]; exists a,b; by split=> //; split.
- move=> [a [b [ha [hb he]]]]; exists (a,b); by split; [split|split].
Qed.

(** Source for [partial_density_product_domain]: common-domain
    qualification for fg in Federer 2.4.10, p. 85.
    The zero-infinity convention concerns existing values and
    does not assign values where either input is undefined. *)
Lemma partial_density_product_domain (R : realType) (X : Type)
    (f h : partial_function X (extended_real_line R)) :
  partial_function_domain (partial_density_product f h) = partial_function_domain f `&` partial_function_domain h.
Proof.
apply/seteqP; split=> x.
- move=> [z hz]; have [a [b [ha [hb _]]]] := (partial_density_product_graph f h x z).1 hz.
  split; [by exists a|by exists b].
- move=> [[a ha] [b hb]]; exists (a*b); apply/partial_density_product_graph.
  exists a,b; by split=> //; split.
Qed.
