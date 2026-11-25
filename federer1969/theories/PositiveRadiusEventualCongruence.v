(** Federer (1969), 3.2.37, pp. 273--274: local positive-radius
    replacements do not change Minkowski contents. These order laws
    use the existing sealed extended supremum and infimum interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedRealBounds PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_limits_eventual_comparison]:
    supporting positive-radius limit comparison in Federer 3.2.37,
    pp. 273--274. A bound on a genuine punctured right
    neighbourhood suffices, even for infinite function values. *)
Lemma positive_radius_limits_eventual_comparison (R:realType)
    (f g:R->\bar R) (d:R):
  (0<d)%R ->(forall r:R,(0<r<d)%R ->f r<=g r) ->
  positive_radius_lower_limit f<=positive_radius_lower_limit g /\
  positive_radius_upper_limit f<=positive_radius_upper_limit g.
Proof.
move=>hd hFG; split.
- apply:extended_real_sup_least=>b [e [he ->]].
  pose delta:=Num.min e d.
  have hDelta:(0<delta)%R by rewrite /delta lt_min he hd.
  have hE:(delta<=e)%R by rewrite /delta ge_min lexx.
  have hD:(delta<=d)%R by rewrite /delta ge_min lexx orbT.
  apply:le_trans _ (positive_radius_lower_ge_level g hDelta).
  apply:extended_real_inf_greatest=>y [r [/andP[hr hrDelta] ->]].
  have hrE:(0<r<e)%R by apply/andP; split=>//; exact:lt_le_trans hrDelta hE.
  have hrD:(0<r<d)%R by apply/andP; split=>//; exact:lt_le_trans hrDelta hD.
  apply:le_trans _ (hFG r hrD).
  apply:extended_real_inf_lower; by exists r.
- apply:extended_real_inf_greatest=>b [e [he ->]].
  pose delta:=Num.min e d.
  have hDelta:(0<delta)%R by rewrite /delta lt_min he hd.
  have hE:(delta<=e)%R by rewrite /delta ge_min lexx.
  have hD:(delta<=d)%R by rewrite /delta ge_min lexx orbT.
  apply:le_trans (positive_radius_upper_le_level f hDelta) _.
  apply:extended_real_sup_least=>y [r [/andP[hr hrDelta] ->]].
  have hrE:(0<r<e)%R by apply/andP; split=>//; exact:lt_le_trans hrDelta hE.
  have hrD:(0<r<d)%R by apply/andP; split=>//; exact:lt_le_trans hrDelta hD.
  apply:le_trans (hFG r hrD) _.
  apply:extended_real_sup_upper; by exists r.
Qed.

(** Source for [positive_radius_limits_eventual_congr]: supporting
    exact eventual replacement in Federer 3.2.37, pp. 273--274.
    No restriction is imposed on values at zero, at negative radii,
    or at large positive radii. *)
Corollary positive_radius_limits_eventual_congr (R:realType)
    (f g:R->\bar R) (d:R):
  (0<d)%R ->(forall r:R,(0<r<d)%R ->f r=g r) ->
  positive_radius_upper_limit f=positive_radius_upper_limit g /\
  positive_radius_lower_limit f=positive_radius_lower_limit g.
Proof.
move=>hd hFG.
have hOne:forall r:R,(0<r<d)%R ->f r<=g r.
  move=>r hr; by rewrite (hFG r hr).
have hTwo:forall r:R,(0<r<d)%R ->g r<=f r.
  move=>r hr; by rewrite (hFG r hr).
have hForward:=positive_radius_limits_eventual_comparison hd hOne.
have hReverse:=positive_radius_limits_eventual_comparison hd hTwo.
split; apply/eqP; rewrite eq_le; apply/andP; split.
- exact:hForward.2.
- exact:hReverse.2.
- exact:hForward.1.
- exact:hReverse.1.
Qed.
