(** Federer (1969), 3.2.46, p. 282: actual
    Jacobian density measures in every exterior degree.
    The original partial differential domain is conull
    and independent of the degree. The density laws of
    2.4.10, p. 85, precede any coarea equality. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations RiemannianTensorUP
  RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianLinearJacobian RiemannianMapDifferential RiemannianMapJacobian
  RiemannianAreaJacobianVolumeMeasurable PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourcePostcomposition PartialExtendedOrderLoci
  MeasureStepIntegralIdentification MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureDensityUP MeasureDensity ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_jacobian_exact_domain]:
    every actual kth Jacobian has precisely the original
    differential domain, supporting 3.2.46, p. 282.
    Zero exterior norm in a high degree supplies no
    value at an undefined differential point. *)
Lemma riemannian_map_jacobian_exact_domain (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) k x :
  partial_function_domain (riemannian_map_jacobian f k) x <->
    partial_function_domain (riemannian_map_differential f) x.
Proof.
split.
- move=> [j [D [hD hValue]]]; by exists D.
- move=> [D hD].
  exists (riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP x))
    (riemannian_tensor_inner hh (set_valP (f x))) k D).
  exists D; by split.
Qed.

(** Source for [riemannian_jacobian_degree_nonnegative_almost]:
    the actual kth Jacobian is nonnegative on a conull
    original source domain, supporting 3.2.46, p. 282.
    The already proved conull differential domain supplies
    every degree, including the target degree needed by
    coarea. Measurability of that other-degree Jacobian
    is not assumed or claimed by this lemma. *)
Theorem riemannian_jacobian_degree_nonnegative_almost (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) k :
  is_riemannian_path_lipschitz f ->
  measure_almost_everywhere (riemannian_hausdorff_measure hg m%:R hp)
    (partial_extended_nonnegative_locus (extended_riemannian_map_jacobian f k)).
Proof.
move=> hLip.
have hMeas := @riemannian_area_jacobian_volume_measurable R m n A B g h hg hh f hp hLip.
apply: (@measure_almost_everywhere_mono R _ _
  (@riemannian_hausdorff_is_measure R m A g hg m%:R hp) _ _ _
  (measurable_function_domain hMeas))=> x [a [r [[D [hD hValue]] hRa]]].
pose j := riemannian_linear_jacobian (riemannian_tensor_inner hg (set_valP x))
  (riemannian_tensor_inner hh (set_valP (f x))) k D.
exists j%:E; split.
- exists j; split; last by [].
  exists D; by split.
- rewrite lee_fin; exact: riemannian_linear_jacobian_nonnegative.
Qed.

(** Source for [is_riemannian_jacobian_density]: independent
    density law from 2.4.10, p. 85, for the
    actual kth Jacobian used in 3.2.46, p. 282.
    This law contains no area or coarea identity. *)
Definition is_riemannian_jacobian_density (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) k (nu : set (riemannian_metric_space hg) -> \bar R) :=
  is_measure_density (riemannian_hausdorff_measure hg m%:R hp)
    (extended_riemannian_map_jacobian f k) nu.

(** Source for [riemannian_jacobian_measure]: the already
    sealed upper-integral density measure of 2.4.10,
    p. 85, with the actual original kth Jacobian
    of 3.2.46, p. 282. No derivative field,
    default Jacobian or transformation equation is selected. *)
Definition riemannian_jacobian_measure (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) k :=
  measure_with_density (riemannian_hausdorff_measure hg m%:R hp) (extended_riemannian_map_jacobian f k).

(** Source for [riemannian_jacobian_measure_laws]: exact
    independent density specification from 2.4.10, p. 85,
    supporting 3.2.46, p. 282, on every original
    source subset, including nonmeasurable ones. *)
Lemma riemannian_jacobian_measure_laws (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) k :
  is_riemannian_jacobian_density f hp k (riemannian_jacobian_measure f hp k).
Proof. exact: measure_with_density_laws. Qed.

(** Source for [riemannian_jacobian_measure_is_measure]:
    actual kth-Jacobian density obeys the measure laws,
    supporting 3.2.46, p. 282, by nonnegativity and
    2.4.10, p. 85. No independent measurability or
    coarea premise for the kth Jacobian is added. *)
Theorem riemannian_jacobian_measure_is_measure (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) k :
  is_riemannian_path_lipschitz f -> is_measure (riemannian_jacobian_measure f hp k).
Proof.
move=> hLip.
exact (@measure_with_density_is_measure R [the choiceType of riemannian_metric_space hg]
  (riemannian_hausdorff_measure hg m%:R hp) (@riemannian_hausdorff_is_measure R m A g hg m%:R hp)
  (extended_riemannian_map_jacobian f k)
  (@riemannian_jacobian_degree_nonnegative_almost R m n A B g h hg hh f hp k hLip)).
Qed.

(** Source for [riemannian_jacobian_measure_measurable]:
    original measurable source sets remain measurable for
    every Jacobian density, supporting 3.2.46, p. 282,
    by 2.4.10, p. 85. This assertion does not
    presuppose the coarea formula or its fibre integral. *)
Lemma riemannian_jacobian_measure_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) k S :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  measure_measurable (riemannian_jacobian_measure f hp k) S.
Proof.
move=> hLip hS.
exact (@measure_with_density_measurable R [the choiceType of riemannian_metric_space hg]
  (riemannian_hausdorff_measure hg m%:R hp) (@riemannian_hausdorff_is_measure R m A g hg m%:R hp)
  (extended_riemannian_map_jacobian f k) S
  (@riemannian_jacobian_degree_nonnegative_almost R m n A B g h hg hh f hp k hLip) hS).
Qed.
