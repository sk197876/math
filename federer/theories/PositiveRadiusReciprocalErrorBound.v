(** Federer (1969), 3.2.38, p. 275: take the full
    positive-radius upper limit and then remove the reciprocal error. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import PositiveRadiusLimits PositiveRadiusLimitBounds
  ExtendedRealReciprocalBounds ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_radius_upper_from_reciprocal_errors]:
    the final limit in Federer 3.2.38, p. 275. Bounds
    at every sufficiently small positive real radius give the
    actual limsup. The finite coefficient is independent of
    the positive integer. No sampled-radius limit is substituted. *)
Lemma positive_radius_upper_from_reciprocal_errors (R:realType)
    (f:R->\bar R) (p K:R):
  0<=K ->
  (forall v:nat,(0<v)%N ->exists d:R,0<d /\forall r:R,0<r<d ->
    (f r<=p%:E+(K/v%:R)%R%:E)%E) ->
  (positive_radius_upper_limit f<=p%:E)%E.
Proof.
move=>hK hBounds.
apply:(@extended_upper_bound_from_scaled_errors R _ p K hK)=>e he.
have [k hk]:=positive_reciprocal_nat_small he.
have [d [hd hRadius]]:=hBounds k.+1 (ltn0Sn k).
apply:le_trans (@positive_radius_upper_eventual_bound R f _ d hd hRadius) _.
rewrite -EFinD lee_fin; apply:lerD (lexx p) _.
exact (ler_wpM2l hK (ltW hk)).
Qed.
