(** Federer (1969), 3.2.13, p. 250: in
    dimension one a positive-radius sphere consists
    of two unit counting atoms. This supporting
    finite integral formula permits arbitrary signed values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialExtendedArithmetic
  MeasureUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAddition MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureCharacteristicIntegral MeasureFiniteRealScaleIntegral MeasureFiniteRealSumIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_atom_pair_subset_integral]: the
    two-point sphere integral in the m=1 case
    of Federer 3.2.13, p. 250, derived
    from characteristic integration and finite signed addition.
    Distinct measurable atoms each have mass one. *)
Lemma unit_atom_pair_subset_integral (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (g:X->R) (a b:X):
  a!=b ->measure_measurable mu [set a] ->measure_measurable mu [set b] ->
  mu [set a]=(1%R)%:E ->mu [set b]=(1%R)%:E ->
  is_measure_subset_integral mu ([set a] `|` [set b]) (real_total_integrand g) (g a+g b)%R%:E.
Proof.
move=>hab ha hb hma hmb.
pose ca:=@CharacteristicFunction.value R X [set a].
pose cb:=@CharacteristicFunction.value R X [set b].
have hca:=@CharacteristicFunction.laws R X [set a].
have hcb:=@CharacteristicFunction.laws R X [set b].
have hIa:=@measure_characteristic_integral R X mu hm [set a] ca hca ha.
have hIb:=@measure_characteristic_integral R X mu hm [set b] cb hcb hb.
rewrite hma in hIa; rewrite hmb in hIb.
have hWa:=@measure_finite_real_total_scale_integral R X mu hm ca 1%R (g a) hIa.
have hWb:=@measure_finite_real_total_scale_integral R X mu hm cb 1%R (g b) hIb.
rewrite mulr1 in hWa; rewrite mulr1 in hWb.
have hSum:=measure_integral_add hm hWa hWb
  (Logic.eq_refl:extended_add (g a)%:E (g b)%:E=Some (g a+g b)%R%:E).
have hI:is_measure_integral mu (real_total_integrand (fun x=>(g a*ca x+g b*cb x)%R)) (g a+g b)%R%:E.
  exact (measure_integral_graph_equivalent (real_total_sum_embedding_graph _ _) hSum).
apply:measure_integral_graph_equivalent _ hI=>x z.
rewrite real_total_integrand_graph partial_function_zero_extension_graph real_total_integrand_graph.
case:(eqVneq x a)=>[hxa|hxa].
- have hOn:ca x = 1%R by apply:(characteristic_on_set hca); exact hxa.
  have hOff:cb x = 0%R.
    apply:(characteristic_off_set hcb)=>hxb; have he:a=b by rewrite -hxa; exact hxb.
    by move:hab; rewrite he eqxx.
  rewrite hOn hOff mulr1 mulr0 addr0 hxa; split=>hz.
  + left; split; first by left.
    exact hz.
  + case:hz=>[[_ hz]|[hn _]]=>//; exfalso; apply:hn; by left.
- have hOff:ca x = 0%R.
    apply:(characteristic_off_set hca)=>h; by move:hxa; rewrite h eqxx.
  rewrite hOff mulr0 add0r.
  case:(eqVneq x b)=>[hxb|hxb].
  + have hOn:cb x = 1%R by apply:(characteristic_on_set hcb); exact hxb.
    rewrite hOn mulr1 hxb; split=>hz.
    * left; split; first by right.
      exact hz.
    * case:hz=>[[_ hz]|[hn _]]=>//; exfalso; apply:hn; by right.
  + have hOffb:cb x = 0%R.
      apply:(characteristic_off_set hcb)=>h; by move:hxb; rewrite h eqxx.
    rewrite hOffb mulr0.
    have hNot:~([set a] `|` [set b]) x.
      move=>[h|h]; [move:hxa|move:hxb]; by rewrite h eqxx.
    split=>hz.
    * right; split=>//; by symmetry.
    * case:hz=>[[hx _]|[_ hz]]; first by exfalso; exact:hNot hx.
      by symmetry.
Qed.
