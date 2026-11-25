(** Federer (1969), 3.3.4, pp. 289–292:
    a finite positive scale comparison preserves
    the ordinary zero-growth alternative. This
    all-positive-radius order argument retains
    extended values and actual aperture dilation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PositiveRightOrderLimit RadialRatioZero
  StructureScaledRadiusWindow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_zero_limit_scaled_comparison]:
    supporting the cone-union zero alternative
    and normalized-ball comparison in Federer
    3.3.4, pp. 289–292. A nonnegative
    original growth function dominated near zero
    by K g(c s) has ordinary limit zero
    when g does; K and c are positive finite. *)
Theorem structure_zero_limit_scaled_comparison (R:realType)
    (f g:R->\bar R) (c K d0:R):
  0<c ->0<K ->0<d0 ->
  (forall s,0<s ->(0<=f s)%E) ->
  (forall s,0<s<d0 ->(f s<=K%:E*g ((c*s)%R))%E) ->
  positive_right_extended_order_limit g 0%E ->
  positive_right_extended_order_limit f 0%E.
Proof.
move=>hc hK hd0 hNonnegative hCompare hLimit.
apply:nonnegative_positive_right_limit_zero=>// e he.
have hThreshold:(0<(e/K)%:E)%E by rewrite lte_fin divr_gt0.
have [b [hb hSmall]]:=hLimit.2 ((e/K)%:E) hThreshold.
have [d [hd hWindow]]:=structure_scaled_radius_window hd0 hb hc.
exists d; split=>// s hs hsd.
have hsD:0<s<d by apply/andP.
have [hOriginal /andP [hPositive hScaled]]:=hWindow s hsD.
apply:(le_lt_trans (hCompare s hOriginal)).
have h:(K%:E*g ((c*s)%R)<K%:E*((e/K)%:E))%E.
  by rewrite lte_pmul2l ?fin_numE ?lte_fin //; exact:hSmall (c*s) hPositive hScaled.
have hCancel:K*(e/K)=e by rewrite mulrC divfK // gt_eqF.
by rewrite -EFinM hCancel in h.
Qed.
