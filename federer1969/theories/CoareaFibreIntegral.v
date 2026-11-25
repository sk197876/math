(** Federer (1969), 3.2.12, pp. 249–250: the
    inner Hausdorff integral is defined precisely on the
    parameters where its actual integral exists. Reuse the
    existing opaque parameterized-integral and subset-integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  HausdorffMeasure PartialFunctionUP PartialZeroExtension ParameterizedIntegral ParameterizedIntegralLaws
  MeasureIntegralUP MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_fibre_integral]: the inner
    integral over f inverse {y} in Federer 3.2.12,
    p. 249. The exact m-n Hausdorff degree and
    original partial integrand are retained; no value is
    assigned to a nonintegrable fibre. *)
Definition coarea_fibre_integral (R:realType) m n
    (f:R_n R m->R_n R n)
    (u:partial_function (R_n R m) (extended_real_line R)):=
  parameterized_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-n))
    (fun y=>partial_function_zero_extension (0:extended_real_line R) [set x|f x=y] u).

(** Source for [coarea_fibre_integral_graph]: the exact
    meaning of the inner integral in Federer 3.2.12,
    pp. 249–250, through the existing abstract integral specification. *)
Lemma coarea_fibre_integral_graph (R:realType) m n
    (f:R_n R m->R_n R n) u y a:
  partial_function_graph (coarea_fibre_integral f u) y a <->
  is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-n)) [set x|f x=y] u a.
Proof. exact:parameterized_integral_specification. Qed.

(** Source for [coarea_fibre_integral_graph_equivalent]:
    replacement of an equal integrand graph in the
    approximation proof of Federer 3.2.12, p. 250.
    All original inner-integrability domains are retained. *)
Lemma coarea_fibre_integral_graph_equivalent (R:realType) m n
    (f:R_n R m->R_n R n) u v:
  (forall x z,partial_function_graph u x z <->partial_function_graph v x z) ->
  forall y a,partial_function_graph (coarea_fibre_integral f u) y a <->
    partial_function_graph (coarea_fibre_integral f v) y a.
Proof.
move=>hEq.
apply:parameterized_integral_graph_equivalent=>y x z.
rewrite !partial_function_zero_extension_graph.
split.
- move=>[[hxy hz]|[hxy hz]].
  + left; split=> //; exact ((hEq x z).1 hz).
  + right; by split.
- move=>[[hxy hz]|[hxy hz]].
  + left; split=> //; exact ((hEq x z).2 hz).
  + right; by split.
Qed.
