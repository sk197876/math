(** Federer (1969), 3.3.4, pp. 289–292:
    finite positive scale comparisons preserve
    the infinite-upper-growth alternative in the
    required direction. Every positive aperture
    cutoff and infinite value remains explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds ExtendedRealOrderTopology
  PositiveRadiusLimits PositiveRadiusLimitBounds StructureScaledRadiusWindow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_infinite_limit_scaled_comparison]:
    supporting the cone lower inclusion and
    the passage from closed to open balls in
    Federer 3.3.4, pp. 289–292. If the
    original f is eventually at most K g(c s)
    and its upper limit is infinity, the
    actual upper limit of g is infinity too. *)
Theorem structure_infinite_limit_scaled_comparison (R:realType)
    (f g:R->\bar R) (c K d0:R):
  0<c ->0<K ->0<d0 ->
  (forall s,0<s<d0 ->(f s<=K%:E*g ((c*s)%R))%E) ->
  positive_radius_upper_limit f=+oo%E ->positive_radius_upper_limit g=+oo%E.
Proof.
move=>hc hK hd0 hCompare hInfinite.
apply/eqP; rewrite eq_le leey /=.
apply:extended_real_inf_greatest=>v [e [he ->]].
case:(pselect ((+oo<=extended_real_sup (positive_radius_values g e))%E))=>hTop; first exact:hTop.
exfalso.
have hFinite:(extended_real_sup (positive_radius_values g e)< +oo)%E.
  rewrite ltNge; apply/negP; exact:hTop.
have [q [hSup _]]:=extended_rationals_order_dense hFinite.
have [d [hd hWindow]]:=structure_scaled_radius_window hd0 he hc.
have hBound:(positive_radius_upper_limit f<=((K*ratr q)%R)%:E)%E.
  apply:(positive_radius_upper_eventual_bound hd)=>s hs.
  have [hOriginal hScaled]:=hWindow s hs.
  have hValue:(g ((c*s)%R)<=(ratr q:R)%:E)%E.
    apply:le_trans _ (ltW hSup); apply:extended_real_sup_upper.
    exists (c*s); by split.
  apply:le_trans (hCompare s hOriginal) _.
  rewrite EFinM; apply:lee_wpmul2l=>//; by rewrite lee_fin ltW.
rewrite hInfinite in hBound.
by have:=lt_le_trans (@ltry R (K*ratr q)) hBound; rewrite ltxx.
Qed.
