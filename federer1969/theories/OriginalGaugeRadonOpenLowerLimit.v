(** Federer (1969), 4.1.5, p. 350:
    the original variation Radon measures
    satisfy the open-set lower-limit inequality.
    Compact positive tests give the original
    open mass; their gauges are lower
    semicontinuous under weak evaluation limits. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP CompactOpenContentUP
  ExtendedRealBoundsUP ExtendedLowerLimit ExtendedLowerLimitMonotone MeasureUP RadonMeasureUP
  RealIntegralFunctionalUP DistributionVariationUP DistributionVariationLowerLimit RadonPositiveCompactOpenContent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [original_gauge_radon_open_lower_limit]: the
    second liminf inequality in Federer
    4.1.5, p. 350, with the
    original Radon variations and every
    open set, including infinite masses. *)
Theorem original_gauge_radon_open_lower_limit (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (values:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:nat->Hom E R^o) (T:Hom E R^o)
    (mu:nat->set X->\bar R) (nu:set X->\bar R)
    (F:nat->(X->R)->R) (H:(X->R)->R):
  locally_compact (@setT X) ->
  (forall i,is_measure (mu i)) ->(forall i,is_radon_measure (mu i)) ->
  is_measure nu ->is_radon_measure nu ->
  (forall i,is_real_integral_functional (mu i)
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) (F i)) ->
  is_real_integral_functional nu
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) H ->
  (forall i f,positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    is_distribution_variation_value NY values (S i) f (F i f)%:E) ->
  (forall f,positive_function_lattice (@compactly_supported_continuous_functions R X) f ->
    is_distribution_variation_value NY values T f (H f)%:E) ->
  (forall phi:E,forall eta:R,0<eta ->exists N,forall i,(N<=i)%N ->`|S i phi-T phi|<eta) ->
  forall V:set X,open V ->(nu V<=extended_lower_limit (fun i=>mu i V))%E.
Proof.
move=>hLocallyCompact hMu hMuRadon hNu hNuRadon hF hH hGauge hLimitGauge hWeak V hV.
have hContent:=@radon_positive_compact_open_content R X nu hNu hNuRadon H hLocallyCompact hH.
apply:(@extended_real_supremum_least R _ (nu V) (hContent V hV)
  (extended_lower_limit (fun i=>mu i V)))=>c [f [hTest ->]].
have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) f.
  split; first exact:hTest.1; move=>x; exact:(andP (hTest.2.1 x)).1.
have hLower:=@distribution_variation_lower_limit R X Y NY E values S T f
  (fun i=>(F i f)%:E) (H f)%:E (fun i=>hGauge i f hPositive) (hLimitGauge f hPositive) hWeak.
have hUpper i:((F i f)%:E<=mu i V)%E.
  have hContentI:=@radon_positive_compact_open_content R X (mu i) (hMu i) (hMuRadon i)
    (F i) hLocallyCompact (hF i).
  apply:(@extended_real_supremum_upper R _ _ (hContentI V hV)).
  exists f; by split.
have hMonotone:=@extended_lower_limit_pointwise_monotone R (fun i=>(F i f)%:E)
  (fun i=>mu i V) hUpper.
exact:le_trans hLower hMonotone.
Qed.
