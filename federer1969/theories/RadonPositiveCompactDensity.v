(** Federer (1969), 4.1.7, p. 358: the
    scalar density of the positive variation is
    nonnegative. This supporting positivity argument
    uses the positive compact approximation of
    2.5.14, p. 108, and dominated convergence
    2.4.9, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureFiniteClosure PartialExtendedOrderLoci RealNormUP NormMetric RealMetricBackground MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalBasic
  FunctionLatticeUP CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP CompactCutoff
  RadonMeasureUP RadonLocallyNull LocallyNullMeasureUP RadonCompactScalarIntegral
  RealIntegralFunctionalUP RealLatticeDensityUP RadonCompactLoneDensity RegularLatticeLoneDensity
  DensePositiveLatticeApproximation DominatedNonnegativePairingLimit
  CharacteristicFunctionUP CharacteristicFunctionSealed TotalScalarLpUP TotalScalarLpCharacteristic
  TotalScalarLpZeroCriterion TotalScalarLpFiniteSeminorm TotalScalarPairing TotalScalarComparison
  TotalScalarMeasurability TotalLoneSummability SummableRealFunctionUP SummableRealArithmetic
  MeasureIntegralUP MeasureIntegralComparison MeasureIntegralUniqueness LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_positive_compact_density_locally_nonnegative]:
    a measurable density representing a positive
    compact-test functional is locally nonnegative
    almost everywhere, supporting Federer 4.1.7,
    p. 358, by 2.5.9 and 2.5.14.
    The density need not have a common bound. *)
Theorem radon_positive_compact_density_locally_nonnegative (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (A:(X->R)->R) (k:X->R):
  is_real_lattice_density mu
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) A k ->
  (forall f,positive_function_lattice (@compactly_supported_continuous_functions R X) f ->0<=A f) ->
  measure_locally_almost_everywhere mu [set x|0<=k x].
Proof.
move=>hk hPositive.
pose L:=@compactly_supported_continuous_functions R X.
pose F:=@radon_compact_integral R X mu hm hr.
have hL:=@compactly_supported_continuous_functions_lattice R X.
have hF:=@radon_compact_integral_laws R X mu hm hr.
have hFplus:is_real_integral_functional mu (positive_function_lattice L) F.
  move=>f hf; exact:hF f hf.1.
have hDense:=@radon_positive_compact_lone_dense R X mu hm hr F hFplus.
have hZero:=@real_total_zero_integral R X mu hm.
have hZeroMeas:=@measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0.
pose E:set X:=[set x|~(0<=k x)].
have hE:measure_measurable mu E.
  exact:measure_measurable_complement
    (@total_scalar_measurable_comparison R X mu hm (fun _=>0) k hZeroMeas hk.1).
pose s:=@CharacteristicFunction.value R X E.
have hs:=@CharacteristicFunction.laws R X E.
have hOn x (hx:E x):s x = 1.
  exact:(characteristic_on_set hs hx).
have hOff x (hx:~E x):s x=0.
  exact:(characteristic_off_set hs hx).
apply/(radon_locally_null_compact_iff hm hr)=>K hK.
pose u:=@compact_cutoff R X K (radon_hausdorff hr) (radon_locally_compact hr) hK.
have hu:=@compact_cutoff_specification R X K (radon_hausdorff hr) (radon_locally_compact hr) hK.
have huPositive:positive_function_lattice L u.
  split; first exact:compact_cutoff_function hu.
  move=>x; exact:(andP (compact_cutoff_range hu x)).1.
have huLone:=@represented_lattice_in_total_lone R X mu hm L F hF u huPositive.1.
pose g x:=u x*s x.
have hg:positive_function_lattice (total_scalar_lp mu 1) g.
  exact:(@positive_lp_characteristic_pieces R X mu hm 1 E s u hs hE
    (conj huLone huPositive.2)).1.
have hgu x:g x<=u x.
  case:(pselect (E x))=>hx.
  - by rewrite /g (@hOn x hx) mulr1.
  - by rewrite /g (@hOff x hx) mulr0; exact:huPositive.2.
have [v [hv hLimit]]:=@dense_positive_lattice_almost_approximation R X L hL F mu hm
  hF hDense u g huPositive hg hgu.
have hBound j x:0<=v j x<=u x.
  apply/andP; split; [exact:(hv j).1.2|exact:(hv j).2].
have hSummable:summable_real_functions mu (fun x=>u x*k x).
  exists (A u); exact:hk.2 u huPositive.
have [b [hi hB0]]:=@dominated_nonnegative_pairing_limit R X mu hm v u g k (fun j=>A (v j))
  hBound huPositive.2 hg.1.2.1 hk.1 hSummable
  (fun j=>hPositive _ (hv j).1) (fun j=>hk.2 _ (hv j).1) hLimit.
have hNonpositive x:g x*k x<=0.
  case:(pselect (E x))=>hx.
  - have hk0:k x<=0.
      rewrite leNgt; apply/negP=>h; apply:hx; exact:ltW h.
    rewrite /g (@hOn x hx) mulr1.
    exact:mulr_ge0_le0 (huPositive.2 x) hk0.
  - by rewrite /g (@hOff x hx) !mulr0 mul0r.
have hOrder:measure_almost_everywhere mu
    (partial_extended_le_locus (real_total_integrand (fun x=>g x*k x))
      (real_total_integrand (fun _=>0))).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _.
  exists (g x*k x)%:E,0%E; split; first by rewrite real_total_integrand_graph.
  split; first by rewrite real_total_integrand_graph.
  rewrite lee_fin; exact:hNonpositive.
have hBUpper:=@measure_integral_monotone R X mu hm _ _ b%:E 0 hi hZero hOrder.
have hBZero:b=0 by apply/eqP; rewrite eq_le hB0 andbT; move:hBUpper; by rewrite lee_fin.
have hAbs:=@real_total_integral_scale R X mu hm (fun x=>g x*k x) b (-1) hi.
have hAbsFun:(fun x=>(-1)*(g x*k x))=(fun x=>`|g x*k x|).
  apply:funext=>x; rewrite mulN1r; symmetry; exact:ler0_norm (hNonpositive x).
rewrite hAbsFun hBZero mulr0 in hAbs.
have hMember:total_scalar_lp mu 1 (fun x=>g x*k x).
  apply:(@summable_real_total_lone R X mu hm); by exists b.
have hNorm:=@total_lone_norm_from_absolute_integral R X mu hm (fun x=>g x*k x) 0
  hMember.2.1 hAbs.
have hAlmost:=@total_scalar_lp_zero_norm_almost_zero R X mu hm 1 (fun x=>g x*k x) hMember hNorm.
apply:(@measure_null_subset R X mu hm _ _ _ hAlmost)=>x [hKx hBad] hGZero.
have hEx:E x:=hBad.
have hU:u x = 1:=compact_cutoff_on_set hu hKx.
change (g x*k x=0) in hGZero.
rewrite /g hU (@hOn x hEx) !mul1r in hGZero.
have hNonnegative:0<=k x.
  by rewrite hGZero lexx.
exact:(hBad hNonnegative).
Qed.
