(** Federer (1969), 2.2.7, p. 64, the printed limsup of local distance
    quotients. We spell out the upper limit as the infimum, over positive
    radii, of the supremum of the punctured local quotients. Suprema and
    infima use the project's sealed extended-real order interface from
    2.1.1. An empty punctured neighborhood has supremum minus infinity, as
    in that convention. Source context and nonnegative-bound convention:
    LipschitzUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds LocalSlopeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_slope_neighborhood_sup]: supporting order
    formulation of Federer 2.2.7, p. 64: the supremum of the
    distance quotients in a punctured ball of radius d about x. *)
Definition metric_slope_neighborhood_sup (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (x : T) (d : R) : \bar R :=
  extended_real_sup [set q | exists y, X y /\ (0 < mdist x y < d)%R /\
    q = ((mdist (f x) (f y) / mdist x y)%R)%:E].

(** Source for [metric_local_slope_limsup]: Federer 2.2.7,
    p. 64, the displayed limsup, expressed by its neighborhood
    infimum of punctured quotient suprema. The expression permits
    infinite limits and isolated points. *)
Definition metric_local_slope_limsup (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (x : T) : \bar R :=
  extended_real_inf [set q | exists d : R, (0 < d)%R /\
    q = metric_slope_neighborhood_sup X f x d].

(** Source for [metric_slope_limsup_radius]: supporting infimum
    approximation for Federer 2.2.7, p. 64: every strict upper
    bound on the limsup bounds a sufficiently small neighborhood
    supremum. This follows from the greatest-lower-bound laws. *)
Lemma metric_slope_limsup_radius (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) x b :
  metric_local_slope_limsup X f x < b -> exists d : R,
    (0 < d)%R /\ metric_slope_neighborhood_sup X f x d < b.
Proof.
move=> hb; case: (pselect (exists d : R, (0 < d)%R /\
    metric_slope_neighborhood_sup X f x d < b))=> h; first exact h.
exfalso; have hl : b <= metric_local_slope_limsup X f x.
  apply: extended_real_inf_greatest=> q [d [hd ->]].
  rewrite leNgt; apply/negP=> hq; apply: h; by exists d.
by move: hb; rewrite ltNge hl.
Qed.

(** Source for [metric_slope_limsup_implies_local_bound]: Federer
    2.2.7, p. 64, supporting equivalence between the printed
    upper-limit inequality and the eventual distance-bound formulation
    used in the segment proof. Center points are handled separately. *)
Lemma metric_slope_limsup_implies_local_bound (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (M : R) :
  (forall x, X x -> metric_local_slope_limsup X f x <= M%:E) ->
  is_metric_local_slope_bound X f M.
Proof.
move=> h x hx L hL.
have hlt : metric_local_slope_limsup X f x < L%:E.
  apply: le_lt_trans (h x hx) _; by rewrite lte_fin.
have [d [hd hs]] := metric_slope_limsup_radius hlt.
exists d; split=> // y hy hdy; case: (eqVneq x y)=> [->|hxy].
- by rewrite !mdistxx mulr0.
- have hp : (0 < mdist x y)%R by rewrite mdist_gt0.
  have hq : ((mdist (f x) (f y) / mdist x y)%R)%:E <=
      metric_slope_neighborhood_sup X f x d.
    apply: extended_real_sup_upper; exists y; split=> //; split=> //.
    by apply/andP; split.
  have hh := ltW (le_lt_trans hq hs).
  by move: hh; rewrite lee_fin (ler_pdivrMr _ _ hp).
Qed.

(** Source for [metric_slope_local_bound_implies_limsup]: Federer
    2.2.7, p. 64, converse of the preceding neighborhood
    formulation. Bounds at every level L>M force the upper limit
    to be at most M, including possible infinite upper limits. *)
Lemma metric_slope_local_bound_implies_limsup (R : realType) (T U : metricType R)
    (X : set T) (f : T -> U) (M : R) :
  is_metric_local_slope_bound X f M ->
  forall x, X x -> metric_local_slope_limsup X f x <= M%:E.
Proof.
move=> h x hx.
have hb L : (M < L)%R -> metric_local_slope_limsup X f x <= L%:E.
  move=> hL; have [d [hd hs]] := h x hx L hL.
  apply: le_trans (extended_real_inf_lower (S :=
    [set q | exists d : R, (0 < d)%R /\ q = metric_slope_neighborhood_sup X f x d]) _) _.
  - exists d; by split.
  - apply: extended_real_sup_least=> q [y [hy [/andP [hp hdy] ->]]].
    rewrite lee_fin (ler_pdivrMr _ _ hp); exact: hs y hy hdy.
case he : (metric_local_slope_limsup X f x)=> [q| |]; last exact: leNye.
- rewrite lee_fin; apply/ler_addgt0Pr=> e hepos.
  have hh := hb (M+e)%R; rewrite he lee_fin in hh.
  apply: hh; by rewrite ltrDl.
- have hh := hb (M+1)%R; rewrite he in hh.
  have hM : (M < M+1)%R by rewrite ltrDl ltr01.
  by have := hh hM.
Qed.
