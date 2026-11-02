(** Federer (1969), 3.2.20, p. 257: replacing the
    original Lipschitz function by a total extension affects no
    source integrand on W. The outer zero extension preserves
    the original domain convention of 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionPostcomposition PartialZeroExtension PartialDensityProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [restricted_partial_area_weight_graph]: supporting
    exact source graph identity for the extension step in Federer
    3.2.20, p. 257. The density may have its own proper
    partial domain; no g-measurability or point value of f outside
    W is introduced. *)
Lemma restricted_partial_area_weight_graph (R : realType) (X Y : Type)
    (W : set X) (F : X -> Y) (g : Y -> \bar R)
    (d : partial_function X (extended_real_line R)) x z :
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) W
    (partial_density_product
      (partial_function_postcompose (partial_function_source_restrict W (partial_function_total F))
        (fun y=>(g y:extended_real_line R))) d)) x z <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) W
    (partial_density_product (partial_function_total (fun x=>(g (F x):extended_real_line R))) d)) x z.
Proof.
case: (pselect (W x))=> hx.
- rewrite !(partial_function_zero_extension_on _ _ _ hx) !partial_density_product_graph.
  have hWeight a : partial_function_graph
      (partial_function_postcompose (partial_function_source_restrict W (partial_function_total F))
        (fun y=>(g y:extended_real_line R))) x a <-> g (F x)=a.
    split.
    + by move=> [y [[hw <-] hVal]].
    + move=> hVal; exists (F x); split; last exact hVal; by split.
  split; move=> [a [b [ha [hb hVal]]]]; exists a,b; split.
  + exact: (hWeight a).1 ha.
  + by split.
  + exact: (hWeight a).2 ha.
  + by split.
- by rewrite !(partial_function_zero_extension_off _ _ _ hx).
Qed.
