(** Project regressions for Federer 2.10.11, p. 176: a compact
    dimension-one obstruction to the printed spherical parenthesis,
    and a constant map with zero multiplicity integral in degree one-half. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import BinaryPrefixMetric BinaryPrefixCompact BinaryVerticalEmbedding MetricProductBackground HausdorffMeasure
  BinarySphericalMultiplicityCounterexample BinaryVerticalSphericalValues RealMetricBackground
  RealHausdorffMultiplicity RealSphericalMultiplicityBound RealHausdorffMeasure
  RealHausdorffMeasureLaws LipschitzUP LipschitzBasic LipschitzConstant
  TopologicalBorel PartialFunctionBasic ExtendedRealOrderTopology MappingMultiplicity
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  NonnegativeExtendedNormOrder RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_spherical_original_hypotheses_regression]:
    concrete project regression for the correction of Federer
    2.10.11, p. 176. The actual binary isometry satisfies every
    original source hypothesis and violates the spherical bound. *)
Example binary_spherical_original_hypotheses_regression (R:realType):
  let h:=@binary_vertical_embedding_lipschitzian R in
  let f:=@binary_vertical_embedding R in
  let X:=binary_prefix_metric R in
  let Y:=metric_product X (real_line_metric R) in
  let beta:=@spherical_measure R Y 1 in
  let F:=partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f setT y:extended_real_line R)) in
  metric_lipschitz_constant h= 1%R /\
  is_measure_integral beta F (measure_lower_integral beta F) /\
    (real_power (metric_lipschitz_constant h) 1)%:E*
      @spherical_measure R X 1 setT<measure_lower_integral beta F /\
  @spherical_measure R X 1 setT= 1 /\
  @spherical_measure R Y 1 (f @` setT)= 2%:E.
Proof.
move=> h f X Y beta F.
have hc:=(@federer_2_10_11_spherical_counterexample R h).2.2.2.2.
split;first exact:hc.1.
split;first exact:hc.2.1.
split;first exact:hc.2.2.
exact:(@binary_vertical_spherical_values R).
Qed.

(** Source for [constant_binary_real_half_multiplicity_regression]:
    zero-Lipschitz-bound regression for the real-degree Hausdorff
    assertion and corrected spherical assertion of Federer 2.10.11,
    p. 176. Collapsing the actual compact binary space to a point
    gives integral zero for each measure in degree one-half. *)
Example constant_binary_real_half_multiplicity_regression (R:realType)
    (hp:(0<=(1/2:R))%R):
  let X:=binary_prefix_metric R in
  let Y:=real_line_metric R in
  let f:X->Y:=fun _=>0%R in
  let F:=partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f setT y:extended_real_line R)) in
  is_measure_integral (@real_hausdorff_measure R Y (1/2:R) hp) F 0 /\
    is_measure_integral (@real_spherical_measure R Y (1/2:R) hp) F 0.
Proof.
move=> X Y f F.
have hpos:(0<(1/2:R))%R by lra.
have hnonzero:((1/2:R)!= 0)%R:=lt0r_neq0 hpos.
have hbound:is_metric_lipschitz_bound setT f 0%R.
  split;first exact:lexx.
  by move=> x y _ _;rewrite /f mdistxx mul0r.
have hlip:=metric_lipschitz_of_bound hbound.
have hL:metric_lipschitz_constant hlip= 0%R.
  exact:(least_metric_lipschitz_unique (metric_lipschitz_constant_specification hlip)
    (@metric_lipschitz_constant_map R X Y setT 0%R)).
have [D [hD hDense]]:=@binary_prefix_metric_separable R.
have hA:borel_set (@setT X) by apply:open_borel_set;exact:openT.
have hH:=@lipschitz_real_hausdorff_multiplicity_bound R X Y f 0%R
  (1/2:R) hp D setT (@binary_prefix_metric_complete R) hD hDense hbound hA.
have hS:=@federer_2_10_11_real_spherical_corrected R X Y f hlip (1/2:R) hp
  D setT (@binary_prefix_metric_complete R) hD hDense hA.
rewrite real_power_zero_base // mul0e in hH.
rewrite hL real_power_zero_base // mulr0 mul0e in hS.
have hZero (mu:set Y->\bar R) (hm:is_measure mu):
    is_measure_integral mu F (measure_lower_integral mu F) ->
    measure_lower_integral mu F<=0 ->is_measure_integral mu F 0.
  move=> hi hb.
  have hn:=@nonnegative_total_integral_value_ge0 R Y mu hm
    (fun y=>(@mapping_multiplicity R X Y f setT y:extended_real_line R)) _
    (fun y=>@mapping_multiplicity_nonnegative R X Y f setT y) hi.
  have he:measure_lower_integral mu F= 0 by apply/eqP;rewrite eq_le hb hn.
  by rewrite -he.
split.
- exact:hZero (@real_hausdorff_measure_is_measure R Y (1/2:R) hp) hH.1 hH.2.
- exact:hZero (@real_spherical_measure_is_measure R Y (1/2:R) hp) hS.1 hS.2.
Qed.
