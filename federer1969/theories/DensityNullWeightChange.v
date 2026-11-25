(** Federer (1969), 3.2.6, pp. 245–246: weights
    may be replaced outside a set null for the speed
    density. Prove the supporting fact directly from the
    density laws, without assuming that the weights are
    measurable for the original source measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialFunctionExtensionUP PartialFunctionExtensionSealed
  PartialDensityProduct PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasurableFunctionUP NonnegativeTotalRepresentative MeasureDensityUP MeasureDensityTransfer
  MeasureSubsetIntegral MeasureIntegralBounds MeasureUpperAlmostEquality ZeroUpperIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_null_real_weight_change]: supporting
    null modification for the reduction to 3.2.5 in Federer
    3.2.6, p. 246. Equal weights almost everywhere
    for a nonnegative density give equal products almost
    everywhere for the original measure. The weights themselves
    need not be measurable for that measure. *)
Theorem density_null_real_weight_change (R:realType) (X:choiceType)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (h:partial_function X (extended_real_line R))
    (g G:X->R):
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  measure_almost_everywhere nu [set x|g x=G x] ->
  measure_almost_equal mu
    (partial_density_product (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) h)
    (partial_density_product (partial_function_total (fun x=>(G x)%:E:extended_real_line R)) h).
Proof.
move=>hNu hh hp hAgree.
have [H [hH0 [hHm hH]]]:=measurable_nonnegative_total_representative hm hh hp.
have hNuH:=@measure_density_almost_equal R X mu nu hm h (partial_function_total H) hNu hH.
pose N:=(~` [set x|g x=G x]).
pose u:=partial_function_zero_extension (0:extended_real_line R) N (partial_function_total H).
pose K:=@PartialFunctionExtension.value X (extended_real_line R) u 0.
have hExt:=@PartialFunctionExtension.laws X (extended_real_line R) u 0.
have hK x:partial_function_graph u x (K x).
  case:(pselect (N x))=>hx.
  - have hVal:partial_function_graph u x (H x).
      apply/partial_function_zero_extension_graph; left; by split.
    have he:K x=H x:=hExt x (H x) hVal.
    by rewrite he.
  - have hVal:partial_function_graph u x 0.
      apply/partial_function_zero_extension_graph; right; by split.
    have he:K x=0:=hExt x 0 hVal.
    by rewrite he.
have hK0 x:0<=K x.
  have hCases:=(partial_function_zero_extension_graph 0 N (partial_function_total H) x (K x)).1 (hK x).
  case:hCases=>[[hx he]|[hx <-]]; last exact:lexx.
  change (H x=K x) in he; by rewrite -he.
have hZero:measure_upper_integral mu (partial_function_total K)=0.
  have hEqual:measure_almost_equal mu u (partial_function_total K).
    apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ (measure_almost_everywhere_true hm))=>x _.
    exists (K x); by split; first exact (hK x).
  rewrite -(@measure_upper_integral_almost_equal R X mu hm u _ hEqual).
  change (measure_subset_upper_integral mu N (partial_function_total H)=0).
  rewrite -(hNuH N); exact hAgree.
have hAE:=nonnegative_zero_upper_integral_almost_zero hm hK0 hZero.
apply:(@measure_almost_everywhere_mono R X mu hm _ _ _
  (measure_almost_everywhere_and hm hH hAE))=>x [[z [hz hHz]] hKx].
have hVal:H x=z:=hHz.
case:(pselect (N x))=>hx.
- have hUx:partial_function_graph u x (H x).
    apply/partial_function_zero_extension_graph; left; by split.
  have hHK:H x=K x:=partial_function_single_valued hUx (hK x).
  have hz0:z=0 by rewrite -hVal hHK hKx.
  exists 0; split; apply/partial_density_product_graph;
    [exists (g x)%:E,z|exists (G x)%:E,z]; split=>//; split=>//; by rewrite hz0 mule0.
- have hEq:g x=G x by apply:contrapT=>hNot; exact (hx hNot).
  exists ((g x)%:E*z); split; apply/partial_density_product_graph.
  + exists (g x)%:E,z; by split=>//; split.
  + exists (G x)%:E,z; split=>//; split=>//; by rewrite hEq.
Qed.
