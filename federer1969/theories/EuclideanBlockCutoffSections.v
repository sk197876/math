(** Federer (1969), 3.2.10, p. 248: supporting
    exact section graph of the image-restricted integrand.
    A product section of a cutoff is the cutoff on
    the corresponding set section, as in 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates ProductSections PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialProductSections PartialZeroExtension
  ExtendedRealOrderTopology RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_block_cutoff_vertical_graph]: the
    transition between the product and inner integrals in
    Federer 3.2.10, p. 248. This is an exact graph
    identity, including points outside the image and empty sections. *)
Lemma euclidean_block_cutoff_vertical_graph (R:realType) n k
    (A:set (R_n R (n+k))) (g:R_n R (n+k)->real_line_metric R) y z r:
  partial_function_graph
    (partial_product_vertical_section (partial_function_precompose (@euclidean_block_join R n k)
      (partial_function_zero_extension (0:extended_real_line R) A
        (partial_function_total (fun w=>(g w)%:E:extended_real_line R)))) y) z r <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
    (product_vertical_section ((@euclidean_block_join R n k) @^-1` A) y)
    (partial_function_total (fun w=>(g (euclidean_block_join (y,w)))%:E:extended_real_line R))) z r.
Proof.
change (partial_function_graph (partial_function_zero_extension (0:extended_real_line R) A
    (partial_function_total (fun w=>(g w)%:E:extended_real_line R))) (euclidean_block_join (y,z)) r <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
    (product_vertical_section ((@euclidean_block_join R n k) @^-1` A) y)
    (partial_function_total (fun w=>(g (euclidean_block_join (y,w)))%:E:extended_real_line R))) z r).
rewrite !partial_function_zero_extension_graph.
by [].
Qed.
