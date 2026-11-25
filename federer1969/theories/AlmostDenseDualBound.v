(** Federer (1969), 4.1.19, p. 377: retain
    the sharp norm when scalar coefficient densities
    are assembled. The countable dense-family argument
    is the one used in 2.5.12,
    pp. 104–105, and 2.9.22, p. 167.
    The actual dual norm is unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground
  NormMetricContinuity NormPowerScalar ContinuousRealFunctional
  RealFunctionalNormUP ContinuousDualUP ConvexProfileClosed NormClosureLaws
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_dual_dense_evaluation_bound]:
    the exact coefficient bound in Federer 4.1.19,
    p. 377, follows from its values on
    a dense family, by continuity as in
    2.5.12, pp. 104–105. The earlier closed-set
    density and least-dual-bound laws supply the result. *)
Theorem continuous_dual_dense_evaluation_bound
    (R : realType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hDual : is_continuous_dual hN ed DN)
    (B : set (real_norm_metric_space hN))
    (hDense : dense B) (phi : D) (c : R) :
  0 <= c -> (forall v, B v -> `|ed phi v| <= c*N v) -> DN phi <= c.
Proof.
move=> hC hBound.
pose E := real_norm_metric_space hN.
have hLeft : continuous (fun v : E => (`|ed phi v| : R^o)).
  move=> v.
  have hFunctional := @continuous_dual_continuous R V N hN D ed DN hDual phi v.
  have hScalar := @NormPowerScalar.real_scalar_norm_identity_continuous R
    (ed phi v).
  have hAbsolute := @real_norm_metric_norm_continuous R R^o
    (fun t : R => `|t|%R) (scalar_absolute_value_norm R) (ed phi v).
  exact: (continuous_comp hFunctional (continuous_comp hScalar hAbsolute)).
have hRight : continuous (fun v : E => (c*N v : R^o)).
  move=> v.
  apply: (@continuousM R E (fun _ => c) (fun z => N z) v).
  - exact: (@cvg_cst [the topologicalType of R^o] c E
      (nbhs v) (nbhs_filter v)).
  - exact: (@real_norm_metric_norm_continuous R V N hN v).
have hClosed : closed [set v : E | `|ed phi v| <= c*N v].
  exact: (@continuous_real_order_constraint_closed R E _ _ hLeft hRight).
have hAll := @dense_closed_superset_all E B
  [set v : E | `|ed phi v| <= c*N v] hDense hClosed hBound.
apply: (real_functional_norm_least (continuous_dual_norm_laws hDual phi) hC).
move=> v; exact: hAll.
Qed.

(** Source for [almost_dense_dual_evaluation_bound]:
    one conull set carries the exact dual
    bound for every coefficient, supporting Federer
    4.1.19, p. 377. Countability is used
    only for the dense testing family, as
    in the preceding representation proof 2.5.12,
    p. 104. The source measure may be infinite. *)
Theorem almost_dense_dual_evaluation_bound
    (R : realType) (X : choiceType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hDual : is_continuous_dual hN ed DN)
    (B : set (real_norm_metric_space hN))
    (hCountable : countable B) (hDense : dense B)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (phi : X -> D) (c : R) :
  0 <= c ->
  (forall v, B v -> measure_almost_everywhere mu
    [set x | `|ed (phi x) v| <= c*N v]) ->
  measure_almost_everywhere mu [set x | DN (phi x) <= c].
Proof.
move=> hC hBound.
have hCommon := @measure_almost_everywhere_countable R X
  (real_norm_metric_space hN) mu hm B
  (fun v => [set x | `|ed (phi x) v| <= c*N v]) hCountable hBound.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hCommon)=> x hx.
exact: (@continuous_dual_dense_evaluation_bound R V D N hN ed DN hDual
  B hDense (phi x) c hC hx).
Qed.
