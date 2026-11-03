(** Federer (1969), 3.2.41, printed p. 278:
    finite measurable source roots are approached from below
    by the actual roots of nonempty compact subsets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanFiniteCompactInner RealRootStrictComparison
  RealPower ExtendedPositivePower FiniteOpenBoxUnionBounds MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_compact_inner_root_strict]: supporting
    actual compact approximation in Federer 3.2.41, p. 278.
    The positive real exponent p generalizes the printed n.
    A nonnegative strict root threshold forces positive compact
    mass and thus a genuinely nonempty compact subset. *)
Lemma euclidean_compact_inner_root_strict (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (p q:R):
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  (@euclidean_lebesgue_measure R n A < +oo)%E ->0<p ->0<=q ->
  (q%:E<extended_positive_power (@euclidean_lebesgue_measure R n A) p^-1)%E ->
  exists K,compact K /\K `<=` A /\K !=set0 /\
    (q%:E<extended_positive_power (@euclidean_lebesgue_measure R n K) p^-1)%E.
Proof.
move=> hA hAF hp hq hRoot.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
have hAFn:mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)); exact hAF.
pose a:R:=fine (mu A).
have hMA:mu A=a%:E by rewrite /a fineK.
have ha:0<=a.
  have h:(0<=mu A)%E:=measure_nonnegative hm A; by rewrite hMA lee_fin in h.
change (is_true (q%:E<extended_positive_power (mu A) p^-1)%E) in hRoot.
rewrite hMA /extended_positive_power lte_fin in hRoot.
have hPower:=(@real_root_strict_power_comparison R a p q ha hp hq).1 hRoot.
have hBelow:((real_power q p)%:E<mu A)%E by rewrite hMA lte_fin.
have [K [hK [hKA hQK]]]:=@euclidean_finite_measurable_compact_inner_strict R n A
  (real_power q p) hA hAF hBelow.
have hPos:(0<mu K)%E.
  apply:le_lt_trans _ hQK; by rewrite lee_fin real_power_nonnegative.
have hNe:K !=set0:=positive_measure_set_nonempty hm hPos.
have hKF:(mu K < +oo)%E:=euclidean_compact_finite hK.
have hKFn:mu K \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm K)); exact hKF.
pose k:R:=fine (mu K).
have hMK:mu K=k%:E by rewrite /k fineK.
have hk:0<=k.
  have h:(0<=mu K)%E:=measure_nonnegative hm K; by rewrite hMK lee_fin in h.
change (is_true ((real_power q p)%:E<mu K)%E) in hQK.
rewrite hMK lte_fin in hQK.
have hRootK:=(@real_root_strict_power_comparison R k p q hk hp hq).2 hQK.
exists K; split; first exact hK.
split; first exact hKA.
split; first exact hNe.
change (is_true (q%:E<extended_positive_power (mu K) p^-1)%E).
by rewrite hMK /extended_positive_power lte_fin.
Qed.
