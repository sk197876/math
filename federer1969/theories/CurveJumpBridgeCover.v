(** Supporting the lower estimate in Federer (1969), 2.10.14, p. 177: bridge
    every missing intermediate scalar level by a one-sided jump interval.
    The first-crossing argument permits arbitrary curves. Later use distance
    from g(a) as the scalar function and bound the bridges by their real
    lengths. This is an expanded proof route for the printed generalisation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveOneSidedJumpUP CurveFirstLevelCrossing
  CurveCrossingJumpBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [right_curve_jump_bridge]: supporting real interval
    [f(x),f(x)+r(x)] for a right-hand jump in 2.10.14, p. 177.
    Its length is the supplied bound r(x), not twice that bound. *)
Definition right_curve_jump_bridge (R : realType) (f r : R -> R) (x : R) :
    set (real_line_metric R) := `[f x,(f x+r x)%R].

(** Source for [left_curve_jump_bridge]: supporting real interval
    [f(x)-l(x),f(x)] for a left-hand jump in 2.10.14, p. 177.
    The two oriented bridges retain the separate printed sums. *)
Definition left_curve_jump_bridge (R : realType) (f l : R -> R) (x : R) :
    set (real_line_metric R) := `[(f x-l x)%R,f x].

(** Source for [curve_jump_bridge_cover]: supporting endpoint estimate
    for 2.10.14, p. 177. Every scalar level between the
    endpoint values is either assumed by f or belongs to a
    bridge at a positive jump bound. Right bridges use [a,b),
    left bridges use (a,b], as in the book's two sums. *)
Theorem curve_jump_bridge_cover (R : realType) (Y : metricType R)
    (g : R -> Y) (f r l : R -> R) (a b : R) : (a<b)%R ->
  (forall t u, (f t-f u<=mdist (g t) (g u))%R) ->
  (forall x, (a<=x<b)%R -> curve_right_jump_size g x<=(r x)%:E) ->
  (forall x, (a<x<=b)%R -> curve_left_jump_size g x<=(l x)%:E) ->
  `[f a,f b] `<=` (f @` (`[a,b] : set (real_line_metric R))) `|`
    ((\bigcup_(x in [set x | (a<=x<b)%R /\ (0<r x)%R]) right_curve_jump_bridge f r x) `|`
     (\bigcup_(x in [set x | (a<x<=b)%R /\ (0<l x)%R]) left_curve_jump_bridge f l x)).
Proof.
move=> hab hf hr hl y; rewrite /= in_itv /= => /andP[hay hyb].
case: (pselect ((f @` (`[a,b] : set (real_line_metric R))) y))=> [hy|hnot]; first by left.
have hya : y!=f a.
  apply/eqP=> he; apply: hnot; exists a; last exact: esym he.
  by rewrite /= in_itv /= lexx (ltW hab).
have hyb' : y!=f b.
  apply/eqP=> he; apply: hnot; exists b; last exact: esym he.
  by rewrite /= in_itv /= (ltW hab) lexx.
have hay' : (f a<y)%R by rewrite lt_neqAle eq_sym hya hay.
have hyb'' : (y<f b)%R by rewrite lt_neqAle hyb' hyb.
have [x hx] := @first_curve_level_crossing_exists R f a b y (ltW hab) hyb''.
have hnxy : f x!=y.
  apply/eqP=> he; apply: hnot; exists x=> //.
  by have [hdom _] := hx; rewrite /= in_itv /=.
case: (ltP y (f x))=> hyx.
- have [hdom hj] := @first_crossing_left_jump_bound R Y g f a b y x hf hx hay' hyx.
  have hbnd := le_trans hj (hl x hdom); rewrite lee_fin in hbnd.
  have hpos : (0<l x)%R by lra.
  right; right; exists x; first by split.
  rewrite /left_curve_jump_bridge /= in_itv /=; apply/andP; split; lra.
- have hxy : (f x<y)%R by rewrite lt_neqAle hnxy hyx.
  have [hdom hj] := @first_crossing_right_jump_bound R Y g f a b y x hf hx hyb'' hxy.
  have hbnd := le_trans hj (hr x hdom); rewrite lee_fin in hbnd.
  have hpos : (0<r x)%R by lra.
  right; left; exists x; first by split.
  rewrite /right_curve_jump_bridge /= in_itv /=; apply/andP; split; lra.
Qed.
