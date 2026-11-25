(** Federer (1969), 4.1.5, p. 350:
    the open-set value of the original
    Radon variation is the 2.5.14 compact
    positive-test supremum. This statement uses
    only the positive compact integral laws,
    retaining infinite open-set masses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP CompactSupportFunctionUP CompactOpenContentUP
  CompactCutoffUP LocalizedCompactCutoffUP LocalizedCompactCutoff RealIntegralFunctionalUP
  RealTotalCharacteristicBounds SummableRealFunctionUP RealIntegralFunctionalUP
  FunctionLatticeLevelMeasurability MeasureUP MeasureBasic RadonMeasureUP RadonBorelRegularity MeasurableFunctionBorel
  TopologicalBorel CountableOrderIntervals ExtendedRealOrderTopology ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_positive_compact_open_content]: the
    original positive compact-test formula for
    open variation masses, Federer 4.1.5,
    p. 350, by 2.5.14, p. 107.
    No Borel variation measure is introduced
    for distributions outside the Radon case. *)
Theorem radon_positive_compact_open_content (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (F:(X->R)->R):
  locally_compact (@setT X) ->
  is_real_integral_functional mu
    (positive_function_lattice (@compactly_supported_continuous_functions R X)) F ->
  is_compact_open_content F mu.
Proof.
move=>hLocallyCompact hF V hV; constructor.
- move=>c [f [[hf [hRange hSupport]] ->]].
  have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) f.
    split=>// x; exact:(andP (hRange x)).1.
  have hIntegral:=hF f hPositive.
  pose P: set X:=[set x|0<f x].
  have hP:measure_measurable mu P.
    rewrite /P -real_total_strict_upper_level.
    apply:(@measurable_function_borel_preimage R X (extended_real_line R) mu hm _ hIntegral.1).
    apply:open_borel_set; exact:order_strict_upper_ray_open.
  have hBound:((F f)%:E<=1%:E*mu P)%E.
    apply:(@real_total_integral_supported_upper_bound R X mu hm P f (F f)%:E 1 hP ltr01 hIntegral).
    + move=>x _; exact:(andP (hRange x)).2.
    + move=>x hx; apply/eqP; rewrite eq_le (andP (hRange x)).1 andbT leNgt; apply/negP; exact:hx.
  rewrite mul1e in hBound; apply:le_trans hBound _.
  apply:(@measure_mono R X mu hm P V)=>x hx; apply:hSupport.
  apply:subset_closure=>hZero; change (is_true (0<f x)) in hx; by move:hx; rewrite hZero ltxx.
- move=>b hUpper.
  apply:(@radon_inner_least R X mu hr V hV b)=>K hK hKV.
  pose g:=@localized_compact_cutoff R X K V (radon_hausdorff hr) hLocallyCompact hK hV hKV.
  have hG:=@localized_compact_cutoff_specification R X K V (radon_hausdorff hr) hLocallyCompact hK hV hKV.
  have hCutoff:=localized_compact_cutoff_laws hG.
  have hTest:is_compact_open_test_function V g.
    split; first exact:compact_cutoff_function hCutoff.
    split; [exact:compact_cutoff_range hCutoff|exact:localized_compact_cutoff_support hG].
  have hPositive:positive_function_lattice (@compactly_supported_continuous_functions R X) g.
    split; first exact:hTest.1; move=>x; exact:(andP (hTest.2.1 x)).1.
  have hKMeasurable:=radon_compact_measurable hm hr hK.
  have hLower:((1:R)%:E*mu K<=(F g)%:E)%E.
    apply:(@real_total_integral_level_lower_bound R X mu hm K g (F g)%:E 1 hKMeasurable ltr01 (hF g hPositive)).
    + move=>x; exact:(andP (compact_cutoff_range hCutoff x)).1.
    + move=>x hx; change (is_true (1<=g x)).
      have hOne:g x= 1:=compact_cutoff_on_set hCutoff hx.
      by rewrite hOne.
  rewrite mul1e in hLower; apply:le_trans hLower _.
  apply:hUpper; exists g; by split.
Qed.
