(** Federer (1969), 3.2.22(3), p. 258:
    exact original-weight and fibre graph comparisons
    for the auxiliary zero-off-source representative. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialDensityProduct MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [supported_weight_actual_graph]: supporting
    preservation of g on W in Federer 3.2.22(3),
    p. 258. Single-valuedness converts agreement at
    one actual value into equality of the original
    graph with the total auxiliary value on W. *)
Lemma supported_weight_actual_graph (X Y:Type) (W:set X) (g:partial_function X Y) (u:X->Y):
  (forall x,W x ->partial_function_graph g x (u x)) ->
  forall x z,W x ->(partial_function_graph g x z <->u x=z).
Proof.
move=>hOn x z hx; split.
- exact:(partial_function_single_valued (hOn x hx)).
- move=>hz; rewrite -hz; exact:(hOn x hx).
Qed.

(** Source for [supported_weight_density_cutoff_graph]:
    the exact source integrand in Federer 3.2.22(3),
    p. 258. Substituting the weight on W does
    not affect any actual partial density value or
    fill in its exceptional undefined domain. *)
Lemma supported_weight_density_cutoff_graph (R:realType) (X:Type) (W:set X)
    (g d:partial_function X (extended_real_line R)) (u:X->extended_real_line R):
  (forall x,W x ->partial_function_graph g x (u x)) ->forall x z,
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) W
    (partial_density_product g d)) x z <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) W
    (partial_density_product (partial_function_total u) d)) x z.
Proof.
move=>hOn x z; have [hx|hx]:=pselect (W x).
- rewrite !(partial_function_zero_extension_on _ _ _ hx) !partial_density_product_graph.
  split; move=>[a [b [ha [hb hz]]]]; exists a,b; split.
  + exact:((@supported_weight_actual_graph X (extended_real_line R) W g u hOn x a hx).1 ha).
  + by split.
  + exact:((@supported_weight_actual_graph X (extended_real_line R) W g u hOn x a hx).2 ha).
  + by split.
- by rewrite !(partial_function_zero_extension_off _ _ _ hx).
Qed.

(** Source for [supported_weight_fibre_graph]: actual fibre
    integrands in Federer 3.2.22(3), p. 258.
    Restrict the global auxiliary map to W and restore
    the original weight on that exact fibre. Outside W
    the auxiliary weight is zero, so no extension value
    can contribute to the fibre integral. *)
Lemma supported_weight_fibre_graph (R:realType) (X Y:Type) (W:set X)
    (F:X->Y) (g:partial_function X (extended_real_line R)) (u:X->extended_real_line R):
  (forall x,W x ->partial_function_graph g x (u x)) ->(forall x,~W x ->u x=0) ->
  forall y x z,
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      [set x|F x=y] (partial_function_total u)) x z <->
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      (mapping_fibre F W y) g) x z.
Proof.
move=>hOn hOff y x z; have [hx|hx]:=pselect (W x).
- have [hValue|hValue]:=pselect (F x=y).
  + have hFibre:mapping_fibre F W y x by split.
    rewrite (@partial_function_zero_extension_on X (extended_real_line R) 0 [set x|F x=y] (partial_function_total u) x z hValue)
      (partial_function_zero_extension_on _ _ _ hFibre).
    symmetry; exact:(@supported_weight_actual_graph X (extended_real_line R) W g u hOn x z hx).
  + have hNotFibre:~mapping_fibre F W y x by move=>[_ h]; exact:hValue h.
    by rewrite (@partial_function_zero_extension_off X (extended_real_line R) 0 [set x|F x=y] (partial_function_total u) x z hValue)
      (partial_function_zero_extension_off _ _ _ hNotFibre).
- have hNotFibre:~mapping_fibre F W y x by move=>[h _]; exact:hx h.
  rewrite (partial_function_zero_extension_off _ _ _ hNotFibre).
  have [hValue|hValue]:=pselect (F x=y).
  + rewrite (@partial_function_zero_extension_on X (extended_real_line R) 0 [set x|F x=y] (partial_function_total u) x z hValue).
    change (u x=z <->z=0); rewrite (hOff x hx); split=>h; exact:esym h.
  + by rewrite (@partial_function_zero_extension_off X (extended_real_line R) 0 [set x|F x=y] (partial_function_total u) x z hValue).
Qed.
