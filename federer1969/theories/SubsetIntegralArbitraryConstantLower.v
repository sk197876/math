(** Federer (1969), 2.4.5, pp. 83–84: the
    upper integral of a characteristic function bounds the
    outer measure of its arbitrary original set. Supporting
    the nonmeasurable-set mass comparison in 3.2.47(3), p. 283. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension
  PartialExtendedOrderLoci CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepIntegralIdentification
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureSubsetIntegral MeasureCharacteristicUpperBound MeasureUpperIntegralScale MeasureUpperIntegralMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_arbitrary_positive_constant_lower]:
    a nonnegative integrand bounded below by c on an
    ARBITRARY A has integral at least c times its
    outer measure, by 2.4.5, pp. 83–84.
    Supporting 3.2.47(3), p. 283; neither A
    measurability nor a null difference from a hull is assumed. *)
Theorem subset_integral_arbitrary_positive_constant_lower (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (A S:set X)
    (u:partial_function X (extended_real_line R)) a (c:R):
  A `<=` S ->(0<c)%R ->
  (forall x,S x ->exists y,partial_function_graph u x y /\0<=y) ->
  (forall x y,A x ->partial_function_graph u x y ->c%:E<=y) ->
  is_measure_subset_integral mu S u a ->c%:E*mu A<=a.
Proof.
move=>hAS hc hDomain hLower hI.
pose chi:=@CharacteristicFunction.value R X A.
have hChi:=@CharacteristicFunction.laws R X A.
pose v:=partial_function_zero_extension (0:extended_real_line R) S u.
pose f:=partial_real_function_embed (partial_function_total chi).
pose g:=partial_extended_function_scale c f.
have hChar:mu A<=measure_upper_integral mu f.
  exact (@measure_characteristic_upper_bound R X mu hm A chi hChi).
have hScale:c%:E*mu A<=measure_upper_integral mu g.
  rewrite /g (@measure_upper_integral_positive_scale R X mu hm c f hc).
  apply:lee_wpmul2l; first by rewrite lee_fin; exact:ltW hc.
  exact hChar.
have hPoint:measure_almost_everywhere mu (partial_extended_le_locus g v).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=>x _.
  have hG:partial_function_graph g x (c%:E*(chi x)%:E).
    exists (chi x)%:E; split; first by exists (chi x); split.
    reflexivity.
  have [hxS|hxS]:=pselect (S x).
  - have [y [hy hPos]]:=hDomain x hxS.
    exists (c%:E*(chi x)%:E),y; split; first exact hG.
    split; first exact ((partial_function_zero_extension_on _ _ _ hxS).2 hy).
    have [hxA|hxA]:=pselect (A x).
    + rewrite /chi (characteristic_on_set hChi hxA) mule1; exact (@hLower x y hxA hy).
    + rewrite /chi (characteristic_off_set hChi hxA) mule0; exact hPos.
  - have hxA:~A x by move=>hx; exact (hxS (hAS x hx)).
    exists (c%:E*(chi x)%:E),0; split; first exact hG.
    split; first exact ((partial_function_zero_extension_off _ _ _ hxS).2 (erefl _)).
    by rewrite /chi (characteristic_off_set hChi hxA) mule0.
have hCompare:=@measure_upper_integral_monotone R X mu hm g v hPoint.
have hValue:measure_upper_integral mu v=a.
  exact (measure_upper_integral_unique (measure_upper_integral_specification mu v) hI.2.1).
rewrite hValue in hCompare; exact (le_trans hScale hCompare).
Qed.
