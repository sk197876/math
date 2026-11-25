(** Finite interpolation under the actual block Fubini
    integral in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric EuclideanLinearMaps
  EuclideanBlockCoordinates EuclideanBlockSetIntegral EuclideanLebesgueDimensions FinitePowerEvaluationRecovery
  MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence SummableRealFunctionUP
  PartialFunctionUP PartialFunctionBasic RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_section_coefficient_integral]: supporting
    finite coefficient integration in Federer 3.2.45,
    p. 279. Independently established nodal set volumes,
    their measurability and their finiteness give the
    actual nodal integrals by Fubini. The proved
    finite linear inverse then gives each coefficient
    integral. The section-volume equations are pointwise
    algebraic identities, not assumptions of coefficient
    integrability or of the desired section inequality.
    Both empty blocks and signed inverse weights remain. *)
Theorem euclidean_section_coefficient_integral (R : realType) m q
    (E G : {linear R_n R (m+q).+1 -> R_n R (m+q).+1})
    (C : inner_metric_space (@euclidean_inner_productP R m) -> R_n R (m+q).+1)
    (S : 'I_(m+q).+1 -> set (inner_metric_space (@euclidean_inner_productP R (m+q)))) :
  cancel E G ->
  (forall j, measure_measurable (@euclidean_lebesgue_measure R (m+q)) (S j)) ->
  (forall j, (@euclidean_lebesgue_measure R (m+q) (S j)< +oo)%E) ->
  (forall y j, @euclidean_lebesgue_measure R q
    [set z | S j (@euclidean_block_join R m q (y,z))]=(E (C y) j)%:E) ->
  forall i, is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (fun y => C y i))
    (G [ffun j : 'I_(m+q).+1 => fine (@euclidean_lebesgue_measure R (m+q) (S j))] i)%:E.
Proof.
move=> hInverse hMeasurable hFinite hSections.
pose N := (m+q)%N.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose u := fun (j : 'I_N.+1) (y : X) => (E (C y) j : real_line_metric R).
pose b := fun j : 'I_N.+1 => fine (@euclidean_lebesgue_measure R N (S j)).
have hIntegrals j : is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (u j)) (b j)%:E.
  have hFubini := @euclidean_block_set_integral R m q (S j) (hMeasurable j).
  have hMassNum : @euclidean_lebesgue_measure R N (S j) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R N) _)); exact: hFinite j.
  have hMass : @euclidean_lebesgue_measure R N (S j)=(b j)%:E by rewrite /b fineK.
  rewrite hMass in hFubini.
  have hGraph y z : partial_function_graph
      (partial_function_total (fun y : X => @euclidean_lebesgue_measure R q
        [set z | S j (@euclidean_block_join R m q (y,z))])) y z <->
      partial_function_graph (real_total_integrand (u j)) y z.
    rewrite real_total_integrand_graph.
    change (@euclidean_lebesgue_measure R q [set z | S j (@euclidean_block_join R m q (y,z))]=z <->
      (E (C y) j)%:E=z).
    by rewrite hSections.
  exact: measure_integral_graph_equivalent hGraph hFubini.
have hValues y j : E (C y) j=u j y by [].
have hIntegral := @finite_power_evaluation_coefficient_integral R N X
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) E G C u b
  hInverse hValues hIntegrals.
move=> i; have h := hIntegral i.
have hValue : (\sum_(j : 'I_N.+1) b j*G (@coordinate_basis R N.+1 j) i)=
    G [ffun j : 'I_N.+1 => b j] i.
  rewrite (@euclidean_linear_expansion R N.+1 G [ffun j : 'I_N.+1 => b j]) sum_ffunE.
  apply: eq_bigr=> j _; by rewrite !ffunE.
by rewrite hValue in h.
Qed.
