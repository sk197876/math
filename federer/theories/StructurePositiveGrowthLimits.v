(** Federer (1969), 3.3.4, pp. 288–289: nonnegative
    cone-growth functions have ordinary zero limit exactly when
    their upper limit is zero. Prove the supporting all-positive-
    scale order statement without finiteness assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds ExtendedRealReciprocalBounds
  PositiveRadiusLimits PositiveRadiusLimitBounds PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_nonnegative_zero_upper_limit_ordinary]:
    supporting ordinary zero-limit assertion (1) of Federer
    3.3.4, p. 288, when a nonnegative cone-growth
    upper limit has been shown to vanish. Every positive
    real aperture remains in the conclusion. *)
Theorem structure_nonnegative_zero_upper_limit_ordinary (R:realType)
    (f:R->\bar R):
  (forall s:R,(0<s)%R ->0<=f s) ->
  positive_radius_upper_limit f=0 ->
  positive_right_extended_order_limit f 0.
Proof.
move=>hNonnegative hZero; split.
- move=>b hb; exists 1%R; split; first exact:ltr01.
  move=>s hs _; exact:(lt_le_trans hb (hNonnegative s hs)).
- move=>b hb.
  have hUpper:positive_radius_upper_limit f<b by rewrite hZero.
  have [d [hd hTail]]:=(positive_radius_upper_lt_iff f b).1 hUpper.
  exists d; split=>// s hs hsd.
  apply:le_lt_trans _ hTail; apply:extended_real_sup_upper.
  exists s; split=>//; by apply/andP.
Qed.

(** Source for [structure_ordinary_zero_limit_upper]: the
    converse supporting identification of the ordinary zero
    alternative with a zero upper limit in Federer 3.3.4,
    pp. 288–289. Nonnegativity and arbitrarily small
    positive finite bounds retain possible infinite values. *)
Theorem structure_ordinary_zero_limit_upper (R:realType) (f:R->\bar R):
  (forall s:R,(0<s)%R ->0<=f s) ->
  positive_right_extended_order_limit f 0 ->
  positive_radius_upper_limit f=0.
Proof.
move=>hNonnegative [_ hSmall].
have hLower:0<=positive_radius_upper_limit f.
  exact:(le_trans (positive_radius_lower_nonnegative hNonnegative)
    (positive_radius_limits_ordered f)).
apply/eqP; rewrite eq_le hLower andbT.
apply:(@extended_real_reciprocal_upper_bound R _ 0%R)=>i; rewrite add0r.
have hPos:(0<((i.+1)%:R:R)^-1)%R by rewrite invr_gt0 ltr0n.
have [d [hd hBound]]:=hSmall (((i.+1)%:R:R)^-1)%:E hPos.
apply:(positive_radius_upper_eventual_bound hd)=>s /andP [hs hsd].
exact:(ltW (hBound s hs hsd)).
Qed.
