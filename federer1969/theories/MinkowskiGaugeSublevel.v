(** Federer (1969), 3.2.35, p. 271:
    relate the actual gauge sublevel to the
    original convex body before identifying its boundary. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import InnerConvex MinkowskiGaugeUP MinkowskiGaugeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_gauge_strict_sublevel_member]:
    supporting S={g<1} for the radial argument
    of Federer 3.2.35, p. 271. A
    strict infimum bound supplies an original positive
    rescaling t<1; convexity with zero then gives
    original membership. Openness is unnecessary in
    this direction and no closed hull is substituted. *)
Lemma minkowski_gauge_strict_sublevel_member (R:realType) (V:lmodType R)
    (S:set V) g x:
  is_minkowski_gauge S g ->is_inner_convex S ->S 0 ->g x<1 ->S x.
Proof.
move=>hG hConvex hZero hx.
have he:0<(1-g x)/2 by rewrite divr_gt0 // subr_gt0.
have [t [ht [hScaled hClose]]]:=@minkowski_gauge_approximation R V S g hG x ((1-g x)/2) he.
have ht1:t<=1 by lra.
have ht0:t!=0 by rewrite gt_eqF.
have hS:=hConvex 0 (t^-1*:x) hZero hScaled t (ltW ht) ht1.
by rewrite scaler0 add0r scalerA (mulfV ht0) scale1r in hS.
Qed.

(** Source for [minkowski_gauge_radial_room_sublevel]:
    supporting the reverse inclusion S subset {g<1}
    in Federer 3.2.35, p. 271. A
    slightly larger radial multiple in the original
    set provides an infimum upper bound strictly
    below one; openness supplies such a multiple
    in the separate normed-space argument. *)
Lemma minkowski_gauge_radial_room_sublevel (R:realType) (V:lmodType R)
    (S:set V) g x c:
  is_minkowski_gauge S g ->1<c ->S (c*:x) ->g x<1.
Proof.
move=>hG hc hScaled.
have hcPositive:0<c:=lt_trans ltr01 hc.
have hInverse:0<c^-1 by rewrite invr_gt0.
have hBound:=@minkowski_gauge_lower R V S g hG x (c^-1) hInverse.
have hS:S ((c^-1)^-1*:x) by rewrite invrK.
have hValue:=hBound hS.
apply:(le_lt_trans hValue _).
by rewrite invf_lt1.
Qed.
