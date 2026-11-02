(** Federer (1969), 3.2.13, p. 250: the
    radial inner integral over {x:|x|=r}. Its
    partial graph contains exactly the parameters where
    the original signed fibre integral exists. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanRadialDifferential EuclideanOneCoordinate CoareaFibreIntegral HausdorffMeasure
  PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension ParameterizedIntegral ParameterizedIntegralLaws
  MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_sphere_integral]: the actual
    inner Hausdorff integral on a radius-r sphere,
    Federer 3.2.13, p. 250. Negative
    radii have empty fibres; no undefined signed
    integral is assigned a value by default. *)
Definition radial_sphere_integral (R:realType) m
    (u:partial_function (R_n R m) (extended_real_line R)):=
  parameterized_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    (fun r:R=>partial_function_zero_extension (0:extended_real_line R)
      [set x|inner_norm (@euclidean_inner_productP R m) x=r] u).

(** Source for [radial_sphere_integral_graph]: precise
    meaning of the inner integral in the first
    formula of Federer 3.2.13, p. 250,
    retaining its actual integrability domain. *)
Lemma radial_sphere_integral_graph (R:realType) m u r a:
  partial_function_graph (@radial_sphere_integral R m u) r a <->
  is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set x|inner_norm (@euclidean_inner_productP R m) x=r] u a.
Proof. exact:parameterized_integral_specification. Qed.

(** Source for [radial_coarea_sphere_graph]: exact
    identification of the coarea fibre and the
    scalar-radius sphere integral, Federer 3.2.13,
    p. 250. It uses both inverse laws
    of the existing scalar identification with R^1. *)
Lemma radial_coarea_sphere_graph (R:realType) m u y a:
  partial_function_graph (coarea_fibre_integral (@euclidean_radial_norm R m) u) y a <->
  partial_function_graph (partial_function_precompose (@euclidean_one_project R)
    (@radial_sphere_integral R m u)) y a.
Proof.
change (partial_function_graph (coarea_fibre_integral (@euclidean_radial_norm R m) u) y a <->
  partial_function_graph (@radial_sphere_integral R m u) (euclidean_one_project y) a).
rewrite coarea_fibre_integral_graph radial_sphere_integral_graph.
have hSet:[set x|euclidean_radial_norm x=y]=
    [set x|inner_norm (@euclidean_inner_productP R m) x=euclidean_one_project y].
  apply/seteqP; split=>x hx.
  - have hh:=congr1 (@euclidean_one_project R) hx.
    by rewrite /euclidean_radial_norm euclidean_one_embedK in hh.
  - exact (eq_trans (congr1 (@euclidean_one_embed R) hx) (euclidean_one_projectK y)).
by rewrite hSet.
Qed.
