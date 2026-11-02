(** Federer (1969), 2.10.22, pp. 184–185: late generators have small
    diameter. The formal cover extraction orders positive costs instead of
    diameters. Its position bound and compactness/ positivity force small
    diameters uniformly in all source rows, giving the printed tail-cover
    use. Source context and proof route: SummablePositiveMaximum.v and
    CompactGeneratorCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded
  CompactGeneratorCostUP CompactGeneratorCostLaws SummableCostEnumerationUP ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cost_array_uniform_small_diameter]: supporting
    uniform late-diameter estimate for the source cover
    array in 2.10.22, pp. 184–185. Inactive
    positions are ignored, without adding an empty
    compact generator to the original family. *)
Theorem compact_cost_array_uniform_small_diameter (R : realType) (X : metricType R) (J : Type)
    (cost : compact_metric_set X -> R) (hc : is_continuous_positive_compact_cost cost)
    (K : set (compact_hausdorff_space X)) (M : R)
    (u : J -> nat -> option (compact_metric_set X)) :
  compact K -> 0<=M ->
  (forall j k C, u j k=Some C -> K C) ->
  (forall j k, k.+1%:R*optional_generator_cost cost (u j k)<=M) ->
  forall eps : R, 0<eps -> exists N, forall j k C, (N<=k)%N -> u j k=Some C ->
    compact_metric_diameter C<eps.
Proof.
move=> hK hM hmem hbudget eps heps.
have [eta [heta hgap]] := @compact_hyperspace_cost_gap R X cost hc K eps hK heps.
have hM1 : 0<M+1 by lra.
have htarget : 0<eta/(M+1) by rewrite divr_gt0.
have [N hN] := real_reciprocal_below htarget.
have hNpos : (0<N.+1%:R :> R) by rewrite ltr0n.
have hNinv : (0<N.+1%:R^-1 :> R) by rewrite invr_gt0.
have hsmall : (M+1)*N.+1%:R^-1<eta.
  rewrite mulrC -ltr_pdivlMr //.
exists N=> j k C hNk hC; apply: hgap (hmem j k C hC) _.
have hkpos : (0<k.+1%:R :> R) by rewrite ltr0n.
have hkinv : (0<k.+1%:R^-1 :> R) by rewrite invr_gt0.
have hkneq : (k.+1%:R : R)!=0 by rewrite gt_eqF.
have hb := hbudget j k; rewrite hC /optional_generator_cost in hb.
have hcBound := ler_wpM2r (ltW hkinv) hb.
rewrite mulrAC mulfV // mul1r in hcBound.
have hrecip : (k.+1%:R^-1<=N.+1%:R^-1 :> R).
  rewrite (lef_pV2 hkpos hNpos) ler_nat; exact hNk.
have hmul := ler_wpM2l hM hrecip.
have hMM : M<=M+1 by lra.
have hlast := ler_wpM2r (ltW hNinv) hMM.
exact: le_lt_trans (le_trans hcBound (le_trans hmul hlast)) hsmall.
Qed.
