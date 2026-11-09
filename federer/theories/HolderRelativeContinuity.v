(** Federer (1969), 3.4.4, p. 318: positive
    Holder estimates imply continuity on the original Cantor set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealMetricBackground MetricSubsetBackground HolderPowerCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holder_real_subset_continuous]: continuity
    in the homeomorphism assertion of 3.4.4, p. 318.
    The map is continuous for the actual subspace metric;
    its values outside the original source are irrelevant. *)
Lemma holder_real_subset_continuous (R:realType) (A:set (real_line_metric R))
    (phi:R->R) (C p:R):
  0<C ->0<p ->
  (forall (x y:real_line_metric R),A x ->A y ->
    `|phi x-phi y|<=C*RealPower.real_power `|x-y| p) ->
  continuous (fun x:metric_subset A=>(phi (val x):real_line_metric R)).
Proof.
move=>hC hP hHolder x U hU.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (phi (val x):real_line_metric R) U) hU.
have hHalf:0<(e:R)/2 by rewrite divr_gt0 // ltr0n.
have [delta [hDelta hSmall]]:=holder_positive_power_cutoff hC hP hHalf.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists delta=>// y hy.
apply:hBall.
change (is_true (`|phi (val x)-phi (val y)|<e)).
have hX:A (val x):=set_valP x.
have hY:A (val y):=set_valP y.
have hBound:=hHolder (val x) (val y) hX hY.
have hDistance:(`|val x-val y|<delta).
  exact:hy.
have hPower:=hSmall `|val x-val y| (normr_ge0 _) (ltW hDistance).
have hHalfLess:(e:R)/2<e by lra.
exact:le_lt_trans (le_trans hBound hPower) hHalfLess.
Qed.
