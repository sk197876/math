(** Federer (1969), 3.2.32, p. 270: supporting
    assembly of the source and target integrals over countably
    many disjoint measurable restrictions, using 2.4.8. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality NonnegativeSum
  TotalCountableNonnegativeIntegral TotalScalarCutoff DisjointScalarCutoffSeries
  DisjointNonnegativeTargetSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_disjoint_coarea_integral]: supporting
    countable source/target integration in Federer 3.2.32,
    p. 270, from 2.4.8, p. 84. Equal local integral
    values sum to the same global value, including infinity.
    These are independent integral hypotheses for this algebraic
    helper; the final theorem discharges them through 3.2.22. *)
Lemma countable_disjoint_coarea_integral (R:realType) (X Y:choiceType)
    (rho:set X->\bar R) (beta:set Y->\bar R) (hr:is_measure rho) (hb:is_measure beta)
    (S:nat->set X) (D:nat->set Y) (J:X->R) (f:Y->extended_real_line R):
  (forall x,(0<=J x)%R) ->(forall y,0<=f y) ->
  (forall i j,i!=j ->forall x,S i x ->S j x ->False) ->
  (forall i j,i!=j ->forall y,D i y ->D j y ->False) ->
  (forall y,~(\bigcup_i D i) y ->f y=0) ->
  (forall i,exists a,
    is_measure_subset_integral rho (S i) (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral beta (partial_function_total (fun y=>if pselect (D i y) then f y else 0)) a) ->
  exists a,is_measure_subset_integral rho (\bigcup_i S i)
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral beta (partial_function_total f) a.
Proof.
move=>hJ hF hSDisj hDDisj hOff hLocal.
have [a hA]:=choice hLocal.
pose u i x:extended_real_line R:=(total_scalar_cutoff (S i) J x)%:E.
pose v i y:extended_real_line R:=if pselect (D i y) then f y else 0.
have hUI i:is_measure_integral rho (partial_function_total (u i)) (a i).
  apply:(measure_integral_graph_equivalent _ (hA i).1)=>x z.
  change (partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
    (S i) (partial_function_total (fun x=>((J x)%:E:extended_real_line R)))) x z <->u i x=z).
  have [hx|hx]:=pselect (S i x).
  - rewrite (partial_function_zero_extension_on _ _ _ hx) /u (total_scalar_cutoff_on J hx); by [].
  - rewrite (partial_function_zero_extension_off _ _ _ hx) /u (total_scalar_cutoff_off J hx).
    change (z=0 <->0=z); split=>h; exact:esym h.
have hUPos i x:0<=u i x.
  rewrite /u lee_fin; exact:(nonnegative_scalar_cutoff (S i) hJ x).
have hVPos i y:0<=v i y.
  rewrite /v; case:pselect=>h; first exact:hF y; exact:lexx.
have hUSum:=total_countable_nonnegative_integral hr (countableP (@setT nat))
  (fun i _ x=>hUPos i x) (fun i _=>hUI i).
have hVSum:=total_countable_nonnegative_integral hb (countableP (@setT nat))
  (fun i _ y=>hVPos i y) (fun i _=>(hA i).2).
have hLoss:rho ((\bigcup_i S i) `\` (\bigcup_i S i))=0.
  rewrite setDv; exact:measure_empty.
have hSub i:S i `<=` (\bigcup_i S i) by move=>x hx; exists i.
have hSeries:=(@disjoint_scalar_cutoff_series R X rho hr (\bigcup_i S i) S J
  hJ hSub hSDisj hLoss).2.
exists (nonnegative_sum setT a); split.
- have hCutIntegral:is_measure_integral rho
      (partial_function_total (fun x=>((total_scalar_cutoff (\bigcup_i S i) J x)%:E:extended_real_line R)))
      (nonnegative_sum setT a).
    apply:(measure_integral_almost_equal hr hUSum).
    apply:(measure_almost_everywhere_mono hr _ hSeries)=>x hx.
    exists (nonnegative_sum setT (fun i=>u i x)); split; first reflexivity; exact:esym hx.
  apply:(measure_integral_graph_equivalent _ hCutIntegral)=>x z.
  change ((total_scalar_cutoff (\bigcup_i S i) J x)%:E=z <->
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      (\bigcup_i S i) (partial_function_total (fun x=>((J x)%:E:extended_real_line R)))) x z).
  have [hx|hx]:=pselect ((\bigcup_i S i) x).
  + rewrite (partial_function_zero_extension_on _ _ _ hx)
      (total_scalar_cutoff_on J hx); by [].
  + rewrite (partial_function_zero_extension_off _ _ _ hx)
      (total_scalar_cutoff_off J hx).
    change (0=z <->z=0); split=>h; exact:esym h.
- have hVEquality y:nonnegative_sum setT (fun i=>v i y)=f y.
    exact:(disjoint_nonnegative_target_series hF hDDisj hOff y).
  apply:(measure_integral_graph_equivalent _ hVSum)=>y z.
  change (nonnegative_sum setT (fun i=>v i y)=z <->f y=z); by rewrite hVEquality.
Qed.
