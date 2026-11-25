(** Compactness step in Federer (1969), 2.8.9, p. 146: directions lie in a
    compact unit sphere, so uniformly separated sets of directions have a
    uniform finite cardinal bound. This module proves the general
    metric-topology fact by a finite cover by balls of radius eta/2. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets functions cardinality reals topology lra.
From Federer Require Import MetricClosedBalls CompactFiniteCover CardinalInjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [compact_separated_cardinal_bound]: supporting compactness
    argument in Federer 2.8.9, p. 146 For each positive separation eta, one
    positive integer bounds every eta-separated subset of K. A supplied
    ambient point is only a choice default; K and the separated subsets may
    be empty. *)
Theorem compact_separated_cardinal_bound (R : realType) (X : metricType R)
    (x0 : X) (K : set X) (eta : R) : compact K -> 0 < eta ->
  exists zeta : nat, (0 < zeta)%N /\ forall B, B `<=` K ->
    (forall x y, B x -> B y -> x <> y -> eta <= mdist x y) ->
    B #<= [set: 'I_zeta].
Proof.
move=> hK he.
have he2 : 0 < eta/2 by rewrite divr_gt0 // ltr0n.
have hcover : K `<=` \bigcup_(c in @setT X) [set x | mdist c x < eta/2].
  by move=> x hx; exists x=> //; rewrite /= mdistxx.
have [F _ hF] := @compact_open_finite_cover X X setT
  (fun c => [set x | mdist c x < eta/2]) K hK
  (fun c _ => metric_open_ball_open c (eta/2)) hcover.
have hchoose : forall x : X, exists c, K x -> c \in F /\ mdist c x < eta/2.
  move=> x; case: (pselect (K x))=> [hx|hx].
  - have [c hc hcx] := hF x hx; by exists c.
  - exists x0; by move=> /hx.
have [f hf] := choice hchoose.
have [n hn] := (finite_setP _).1 (finite_fset F).
have hFn : [set` F] #<= [set: 'I_n].
  have h := card_eq_trans hn (@card_II n).
  by move: h; rewrite card_eq_le=> /andP[].
have hnn : [set: 'I_n] #<= [set: 'I_n.+1].
  by rewrite -(card_le_eql (@card_II n)) -(card_le_eqr (@card_II n.+1)) card_le_II leqnSn.
exists n.+1; split; first exact: ltn0Sn.
move=> B hBK hsep.
have hBF : B #<= [set` F].
  apply: (@cardinal_bound_of_injection X X B [set` F] f).
  - move=> x hx; exact: (hf x (hBK x hx)).1.
  - move=> x y hx hy hxy.
    have hxB := set_mem hx; have hyB := set_mem hy.
    apply: contrapT=> hne.
    have hlow := hsep x y hxB hyB hne.
    have hx' := (hf x (hBK x hxB)).2.
    have hy' := (hf y (hBK y hyB)).2.
    have htri := metric_triangle x (f x) y.
    rewrite (metric_sym x (f x)) in htri.
    rewrite -hxy in hy'.
    have hsum := ltrD hx' hy'; rewrite -splitr in hsum.
    by have := le_lt_trans hlow (le_lt_trans htri hsum); rewrite ltxx.
exact: card_le_trans hBF (card_le_trans hFn hnn).
Qed.
