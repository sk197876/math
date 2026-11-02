(** Federer (1969), 3.2.37, pp. 273--274: positive-degree
    singleton tubes have vanishing normalized volume. This scalar
    helper takes the full positive-radius limit, with no sequence
    reduction or unproved real-power limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra.
From Federer Require Import PositiveRadiusLimits PositiveRadiusLimitBounds
  ExtendedRealReciprocalBounds PositiveUniformErrorRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [small_positive_power_le_radius]: scalar support
    for the positive-degree singleton computation of Federer
    3.2.37, pp. 273--274. For 0<r<=1, every positive natural
    power is at most r. *)
Lemma small_positive_power_le_radius (R:realType) (m:nat) (r:R):
  (0<m)%N ->(0<r)%R ->(r<=1)%R ->(r^+m<=r)%R.
Proof.
move=>hm hr hr1.
have hP k:(r^+k<=1)%R.
  elim:k=>[|k ih]; first by rewrite expr0.
  rewrite exprS; apply:le_trans (ler_wpM2l (ltW hr) ih) _.
  by rewrite mulr1.
case:m hm=>[|k] hm; first by rewrite ltn0 in hm.
rewrite exprS; apply:le_trans (ler_wpM2l (ltW hr) (hP k)) _.
by rewrite mulr1.
Qed.

(** Source for [positive_radius_natural_power_limit]: both actual
    upper and lower radius limits of c*r^m are zero for finite
    nonnegative c and positive natural m, supporting Federer
    3.2.37, pp. 273--274. Every radius cutoff is proved locally. *)
Lemma positive_radius_natural_power_limit (R:realType) (c:R) (m:nat):
  (0<=c)%R ->(0<m)%N ->
  positive_radius_upper_limit (fun r:R=>(c*r^+m)%:E)=0 /\
  positive_radius_lower_limit (fun r:R=>(c*r^+m)%:E)=0.
Proof.
move=>hc hm.
have hLower:0<=positive_radius_lower_limit (fun r:R=>(c*r^+m)%:E).
  apply:positive_radius_lower_nonnegative=>r hr.
  rewrite lee_fin; exact:mulr_ge0 hc (ltW (exprn_gt0 _ hr)).
have hUpper:positive_radius_upper_limit (fun r:R=>(c*r^+m)%:E)<=0.
  apply:(@extended_real_reciprocal_upper_bound R _ 0%R)=>N.
  pose e:=((N.+1%:R:R)^-1)%R.
  have he:(0<e)%R by rewrite /e invr_gt0 ltr0n.
  have [d [hd [hd1 hError]]]:=positive_uniform_error_radius_exists hc he.
  apply:positive_radius_upper_eventual_bound hd _=>r /andP[hr hrd].
  rewrite add0r lee_fin.
  have hr1:(r<=1)%R:=le_trans (ltW hrd) hd1.
  have hPow:=small_positive_power_le_radius hm hr hr1.
  have hCost:=ler_wpM2l hc hPow.
  have hRadius:=ler_wpM2l hc (ltW hrd).
  rewrite mulrC in hError.
  exact:le_trans hCost (le_trans hRadius (ltW hError)).
have hOrder:=positive_radius_limits_ordered (fun r:R=>(c*r^+m)%:E).
split; apply/eqP; rewrite eq_le; apply/andP; split=>//.
- exact:le_trans hLower hOrder.
- exact:le_trans hOrder hUpper.
Qed.
