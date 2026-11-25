(** Federer (1969), 4.1.19, p. 377: choose
    a representative with the sharp pointwise
    bound after proving its almost-everywhere bound.
    Original L1 integral values survive the
    null modification by 2.3.2 and 2.4.3(2),
    pp. 73 and 81. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureIntegralUP
  MeasureIntegralAlmostEquality SummableRealFunctionUP
  SummableFieldSealed SummableFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_dual_bounded_representative]:
    the bounded measurable form representatives in
    Federer 4.1.19, p. 377, can
    satisfy the sharp pointwise bound everywhere.
    Only the original null exceptional set is
    changed; all original raw L1 actions remain exact. *)
Theorem summable_dual_bounded_representative
    (R : realType) (X : topologicalType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R) (hDN : is_real_norm DN)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : Hom (@SummableField.space R X V N hN mu hm) R^o)
    (phi : X -> D) (c : R) :
  0 <= c -> is_measurable_normed_function mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space hDN))) ->
  measure_almost_everywhere mu [set x | DN (phi x) <= c] ->
  (forall w : @SummableField.space R X V N hN mu hm,
    is_measure_integral mu (real_total_integrand (fun x =>
      ed (phi x) (@summable_field_value R X V N hN mu hm w x))) (F w)%:E) ->
  exists psi : X -> D,
    is_measurable_normed_function mu
      (partial_function_total (fun x => (psi x : real_norm_metric_space hDN))) /\
    (forall x, DN (psi x) <= c) /\
    measure_almost_equal mu
      (partial_function_total (fun x => (phi x : real_norm_metric_space hDN)))
      (partial_function_total (fun x => (psi x : real_norm_metric_space hDN))) /\
    forall w : @SummableField.space R X V N hN mu hm,
      is_measure_integral mu (real_total_integrand (fun x =>
        ed (psi x) (@summable_field_value R X V N hN mu hm w x))) (F w)%:E.
Proof.
move=> hC hPhi hAlmost hAction.
pose psi (x : X) : D := if pselect (DN (phi x) <= c) then phi x else 0.
have hOn (x : X) (hx : DN (phi x) <= c) : psi x = phi x.
  by rewrite /psi; case: pselect.
have hEqual : measure_almost_equal mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space hDN)))
    (partial_function_total (fun x => (psi x : real_norm_metric_space hDN))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)=> x hx.
  exists (phi x); split; first exact: erefl.
  change (psi x=phi x); exact: (@hOn x hx).
have hMeas := @measurable_normed_almost_equal R X D DN hDN mu hm _ _
  hPhi hEqual.
exists psi; split; first exact: hMeas.
split.
- move=> x; rewrite /psi; case: pselect=> [hx|hx]; first exact: hx.
  by rewrite (real_seminorm_zero hDN.1).
split; first exact: hEqual.
move=> w; apply: (@measure_integral_almost_equal R X mu hm _ _ _
  (@hAction w)).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)=> x hx.
exists (ed (phi x) (@summable_field_value R X V N hN mu hm w x))%:E.
split; apply/real_total_integrand_graph; first exact: erefl.
by rewrite (@hOn x hx).
Qed.
