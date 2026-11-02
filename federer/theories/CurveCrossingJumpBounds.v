(** Supporting Federer (1969), 2.10.14, p. 177: a missing intermediate level
    at a first crossing is bounded by the appropriate one-sided jump. Use
    scalar distance projections later; the auxiliary statement accepts any
    scalar function whose increments are bounded by the curve's distances.
    This supplies details for a proof of the printed generalisation, not an
    additional claim attributed to Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import CurveOneSidedJumpUP CurveFirstLevelCrossing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [first_crossing_left_jump_bound]: supporting
    downward bridge from the value at a first crossing in
    2.10.14, p. 177. If f(x)>y, earlier nearby values
    are at most y, so alpha_-(x) covers f(x)-y. *)
Lemma first_crossing_left_jump_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (f : R -> R) (a b y x : R) :
  (forall t u, (f t-f u<=mdist (g t) (g u))%R) ->
  is_first_curve_level_crossing f a b y x -> (f a<y)%R -> (y<f x)%R ->
  (a<x<=b)%R /\ ((f x-y)%R)%:E<=curve_left_jump_size g x.
Proof.
move=> hf [/andP[hax hxb] [hbefore hnear]] hay hyx.
have hneq : x!=a.
  apply/eqP=> he; rewrite he in hyx.
  by have hh := lt_trans hay hyx; rewrite ltxx in hh.
have hax' : (a<x)%R by rewrite lt_neqAle eq_sym hneq hax.
split; first by rewrite hax' hxb.
apply: curve_one_sided_jump_lower_bound=> d hd.
pose v : R := Order.max a (x-d)%R.
have hvx : (v<x)%R by rewrite /v gt_max; apply/andP; split; lra.
have [hvt htx] := midf_lt hvx.
pose t : R := ((v+x)/2)%R.
have htx' : (t<x)%R := htx.
have hav : (a<=v)%R by rewrite /v le_max lexx.
have hdv : (x-d<=v)%R by rewrite /v le_max lexx orbT.
have hat : (a<=t)%R := le_trans hav (ltW hvt).
have hdt : (x-d<t)%R := le_lt_trans hdv hvt.
have ht : (0<curve_side_offset false x t<d)%R.
  rewrite /curve_side_offset /=; apply/andP; split; lra.
exists t; split=> //; rewrite lee_fin.
have hfy := hbefore t hat htx.
have hdist := hf x t; rewrite metric_sym in hdist.
lra.
Qed.

(** Source for [first_crossing_right_jump_bound]: supporting
    upward bridge after a first crossing in 2.10.14, p. 177.
    If f(x)<y, crossing values occur arbitrarily close to
    its right, so alpha_+(x) covers y-f(x). *)
Lemma first_crossing_right_jump_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (f : R -> R) (a b y x : R) :
  (forall t u, (f t-f u<=mdist (g t) (g u))%R) ->
  is_first_curve_level_crossing f a b y x -> (y<f b)%R -> (f x<y)%R ->
  (a<=x<b)%R /\ ((y-f x)%R)%:E<=curve_right_jump_size g x.
Proof.
move=> hf [/andP[hax hxb] [hbefore hnear]] hyb hxy.
have hneq : x!=b.
  apply/eqP=> he; rewrite he in hxy.
  by have hh := lt_trans hxy hyb; rewrite ltxx in hh.
have hxb' : (x<b)%R by rewrite lt_neqAle hneq hxb.
split; first by rewrite hax hxb'.
apply: curve_one_sided_jump_lower_bound=> d hd.
have [t [/andP[hxt htb] [htd hyt]]] := hnear d hd.
have hnt : x!=t.
  apply/eqP=> he; rewrite -he in hyt.
  by have hh := lt_trans hxy hyt; rewrite ltxx in hh.
have hxt' : (x<t)%R by rewrite lt_neqAle hnt hxt.
have ht : (0<curve_side_offset true x t<d)%R.
  rewrite /curve_side_offset /=; apply/andP; split; lra.
exists t; split=> //; rewrite lee_fin.
have hdist := hf t x; lra.
Qed.
