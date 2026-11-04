(** Federer (1969), 3.2.12, pp. 249–250, extended
    by 3.2.46, p. 282: the actual inner integral
    uses the original Riemannian Hausdorff measure on the
    whole original fibre. Existing sealed parameterized
    integration preserves precisely its integrability domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  PartialFunctionUP PartialZeroExtension ParameterizedIntegral ParameterizedIntegralLaws
  MeasureIntegralUP MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_riemannian_coarea_fibre_integral]:
    the actual inner integral over f inverse {y} in
    3.2.12, p. 249, with the Riemannian metric
    required by 3.2.46, p. 282. This independent
    value law contains no coarea equality or assumed
    fibre-integrability conclusion. *)
Definition has_riemannian_coarea_fibre_integral (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=(m-n)%:R :> R)%R)
    (u : partial_function (riemannian_metric_space hg) (extended_real_line R)) y a :=
  is_measure_subset_integral (riemannian_hausdorff_measure hg (m-n)%:R hp) [set x | f x=y] u a.

(** Source for [riemannian_coarea_fibre_integral]: the
    actual partial inner-integral function of 3.2.12,
    pp. 249–250, in 3.2.46, p. 282. It
    reuses the already sealed parameterized integral; no
    value is assigned to a nonintegrable original fibre. *)
Definition riemannian_coarea_fibre_integral (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=(m-n)%:R :> R)%R)
    (u : partial_function (riemannian_metric_space hg) (extended_real_line R)) :=
  parameterized_integral (riemannian_hausdorff_measure hg (m-n)%:R hp)
    (fun y=>partial_function_zero_extension (0 : extended_real_line R) [set x | f x=y] u).

(** Source for [riemannian_coarea_fibre_integral_graph]:
    exact original inner-integral graph in 3.2.12,
    pp. 249–250, supporting 3.2.46, p. 282.
    Missing, signed infinite and finite fibre-integral
    values keep their actual defining meaning. *)
Lemma riemannian_coarea_fibre_integral_graph (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=(m-n)%:R :> R)%R) u y a :
  partial_function_graph (riemannian_coarea_fibre_integral f hp u) y a <->
    has_riemannian_coarea_fibre_integral f hp u y a.
Proof. exact: parameterized_integral_specification. Qed.

(** Source for [riemannian_coarea_fibre_integral_graph_equivalent]:
    exact graph replacement of the original partial
    weight in the proof of 3.2.12, p. 250,
    with actual fibre measure in 3.2.46, p. 282.
    No inner-integrability or total-domain premise is added. *)
Theorem riemannian_coarea_fibre_integral_graph_equivalent (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=(m-n)%:R :> R)%R) u v :
  (forall x z, partial_function_graph u x z <-> partial_function_graph v x z) ->
  forall y a, partial_function_graph (riemannian_coarea_fibre_integral f hp u) y a <->
    partial_function_graph (riemannian_coarea_fibre_integral f hp v) y a.
Proof.
move=> hAgreement.
apply: parameterized_integral_graph_equivalent=> y x z.
rewrite !partial_function_zero_extension_graph; split.
- move=> [[hx hz]|[hx hz]].
  + left; split; first exact hx; exact: (hAgreement x z).1 hz.
  + right; by split.
- move=> [[hx hz]|[hx hz]].
  + left; split; first exact hx; exact: (hAgreement x z).2 hz.
  + right; by split.
Qed.
