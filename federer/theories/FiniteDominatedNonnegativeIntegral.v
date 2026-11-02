(** Federer (1969), 3.2.31, p. 269: supporting integration of
    the Hausdorff image bound from 3.2.30, p. 268. The finite
    nonnegative integral provides the countably measurable support
    needed to transfer completed measurability between two measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasurableFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness CountablyMeasurableUP SummableCountableMeasurability
  BorelRegularMeasureUP TopologicalBorel BorelDominatedNonnegativeIntegral MeasureScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_dominated_nonnegative_integral]: supporting
    the rescaled integral estimate in Federer 3.2.31, p. 269,
    using 2.4.4(3), p. 82, and the Borel sandwich in 2.2.3,
    p. 61. Setwise domination by a positive finite constant
    bounds the actual integral and proves its existence. Only
    the dominating measure requires Borel regularity; no general
    implication between completed measurable sigma algebras is used. *)
Theorem finite_dominated_nonnegative_integral (R:realType) (X:topologicalType)
    (mu nu:set X->\bar R) (hm:is_measure mu) (hn:is_measure nu)
    (hr:is_borel_regular_measure mu) (f:X->extended_real_line R) (a c:R):
  (0<c)%R ->
  (forall B,borel_set B ->measure_measurable nu B) ->
  (forall A,nu A<=c%:E*mu A) ->
  (forall x,0<=f x) ->
  is_measure_integral mu (partial_function_total f) a%:E ->
  exists b,is_measure_integral nu (partial_function_total f) b /\
    0<=b /\b<=c%:E*a%:E.
Proof.
move=>hc hB hBound hp hi.
have hci:(0<c^-1)%R by rewrite invr_gt0.
pose eta:=measure_scale c^-1 nu.
have hEta:is_measure eta:=@measure_scale_is_measure R X nu c^-1 hn hci.
have hEtaB B (h:borel_set B):measure_measurable eta B.
  exact (@measure_scale_measurable R X nu hn c^-1 B (hB B h)).
have hDom A:eta A<=mu A.
  have hciE:0<=(c^-1)%:E by rewrite lee_fin; exact:ltW hci.
  have h:=lee_wpmul2l hciE (hBound A).
  by rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in h.
have hCount:=@measure_summable_countably_measurable R X mu hm
  (partial_function_total f) (ex_intro _ a hi).
have hSet:partial_function_nonzero_locus (0:extended_real_line R)
    (partial_function_total f)=[set x|f x<>0].
  apply/seteqP; split=>x.
  - move=>[y [hy hny]]; change (f x<>0); by rewrite (hy:f x=y).
  - move=>hx; exists (f x); by split.
have hSupport:measure_countably_measurable mu [set x|f x<>0].
  rewrite -hSet; exact:countably_measurable_function_locus hCount.
have [d [hD [hd0 hda]]]:=@borel_dominated_nonnegative_integral R X mu eta
  hm hEta hr f a%:E hEtaB hDom hp hSupport hi.
have hScaled:=@measure_scale_integral R X eta hEta c hc _ d hD.
have hCancel:measure_scale c eta=nu.
  by apply:funext=>A; rewrite /eta /measure_scale muleA -EFinM mulfV ?(gt_eqF hc) // mul1e.
rewrite hCancel in hScaled.
exists (c%:E*d); split; first exact hScaled.
split.
- apply:mule_ge0=>//; by rewrite lee_fin; exact:ltW hc.
- apply:lee_wpmul2l=>//; by rewrite lee_fin; exact:ltW hc.
Qed.
