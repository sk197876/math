(** Federer (1969), 2.4.10, p. 85: restricting
    an integrand before multiplication by a total density
    is the same original subset product. This supports
    the source normalization of 3.2.46, p. 282,
    and respects zero times infinity without extending
    an undefined original partial function. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cutoff_total_density_product_graph]:
    exact subset-product graph law supporting 2.4.10,
    p. 85, as used in 3.2.46, p. 282.
    The total density may have infinite or zero values;
    no value of u is assigned outside its original domain. *)
Lemma cutoff_total_density_product_graph (R : realType) (X : Type)
    (u : partial_function X (extended_real_line R)) (d : X -> extended_real_line R)
    (S : set X) x z :
  partial_function_graph (partial_density_product
    (partial_function_zero_extension (0 : extended_real_line R) S u)
    (partial_function_total d)) x z <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) S
    (partial_density_product u (partial_function_total d))) x z.
Proof.
case:(pselect (S x))=> hx.
- rewrite (partial_function_zero_extension_on _ _ _ hx) !partial_density_product_graph.
  split.
  + move=> [a [b [ha [hb hValue]]]]; exists a,b; split; last by split.
    exact:(partial_function_zero_extension_on _ _ _ hx).1 ha.
  + move=> [a [b [ha [hb hValue]]]]; exists a,b; split; last by split.
    exact:(partial_function_zero_extension_on _ _ _ hx).2 ha.
- rewrite (partial_function_zero_extension_off _ _ _ hx) partial_density_product_graph.
  split.
  + move=> [a [b [ha [hb hValue]]]].
    have ha0 : a=0 := (partial_function_zero_extension_off _ _ _ hx).1 ha.
    by rewrite ha0 mul0e in hValue; exact:esym hValue.
  + move=> ->; exists 0,(d x); split.
    * apply/partial_function_zero_extension_graph; right; by split.
    * split; first by []; exact:mul0e.
Qed.
