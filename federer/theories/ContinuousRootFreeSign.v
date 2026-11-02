(** Federer (1969), 3.2.6, p. 246: between
    consecutive points of a finite level fibre, continuity
    keeps the same side of the level. This supporting
    one-dimensional topological step is the intermediate-value
    argument in the signed crossing count. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology normedtype lra.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_root_free_sign]: the root-free
    interval observation behind the signed multiplicity in
    Federer 3.2.6, p. 246. Both endpoints are
    retained; the interval may be degenerate. *)
Lemma continuous_root_free_sign (R:realType) (f:R->R) (a b y:R):
  a<=b -> continuous (f:real_line_metric R->real_line_metric R) ->
  (forall x,a<=x -> x<=b -> f x!=y) ->
  Num.sg (f b-y)=Num.sg (f a-y).
Proof.
move=>hab hCont hNo.
have hfa:f a!=y:=hNo a (lexx _) hab.
have hfb:f b!=y:=hNo b hab (lexx _).
have hNoCross:~exists x,(`[a,b]:set (real_line_metric R)) x /\ f x=y.
  move=>[x [hx hfx]]; move:hx; rewrite /= in_itv /= =>/andP [hax hxb].
  have hh:=hNo x hax hxb; by rewrite hfx eqxx in hh.
case:(ltP (f a) y)=>hBelow.
- have hBelowB:f b<y.
    case:(ltP (f b) y)=>// hAbove.
    have hOrder:f a<=f b by lra.
    have hBounds:Num.min (f a) (f b)<=y<=Num.max (f a) (f b).
      by rewrite min_l // max_r // (ltW hBelow) hAbove.
    have [x hx hfx]:=@IVT R f a b y hab (continuous_subspaceT hCont) hBounds.
    exfalso; apply:hNoCross; by exists x.
  by rewrite (ltr0_sg (_:f b-y<0)) ?subr_lt0 // (ltr0_sg (_:f a-y<0)) ?subr_lt0.
- have hAboveA:y<f a by rewrite lt_neqAle eq_sym hfa hBelow.
  have hAboveB:y<f b.
    case:(ltP y (f b))=>// hBelowB.
    have hOrder:f b<=f a by lra.
    have hBounds:Num.min (f a) (f b)<=y<=Num.max (f a) (f b).
      by rewrite min_r // max_l // hBelowB (ltW hAboveA).
    have [x hx hfx]:=@IVT R f a b y hab (continuous_subspaceT hCont) hBounds.
    exfalso; apply:hNoCross; by exists x.
  by rewrite (gtr0_sg (_:0<f b-y)) ?subr_gt0 // (gtr0_sg (_:0<f a-y)) ?subr_gt0.
Qed.
