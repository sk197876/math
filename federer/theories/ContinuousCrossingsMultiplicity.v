(** Federer (1969), 3.2.7, p. 246: supporting
    finite crossing count for the oscillatory example.
    Apply the intermediate-value theorem on disjoint
    intervals and compare the resulting actual fibre
    with finite counting measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground MappingMultiplicity CountingInjectionBound CountingFinitePredicate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_disjoint_crossings_multiplicity_bound]:
    finite level-count estimate for the third example
    of Federer 3.2.7, p. 246. The source
    intervals are closed and pairwise disjoint, so
    each intermediate value supplies a different root. *)
Theorem continuous_disjoint_crossings_multiplicity_bound (R:realType)
    (f:R->R) (A:set (real_line_metric R)) (n:nat)
    (l r:'I_n->R) (y:R):
  continuous (f:real_line_metric R->real_line_metric R) ->
  (forall i,l i<=r i) ->
  (forall i,(`[l i,r i]:set (real_line_metric R)) `<=` A) ->
  (forall i j,i!=j -> forall x,l i<=x<=r i -> l j<=x<=r j -> False) ->
  (forall i,f (r i)<=y<=f (l i)) ->
  (n%:R%:E<=@mapping_multiplicity R [the choiceType of real_line_metric R] R f A y)%E.
Proof.
move=>hc hl hA hd hy.
have hExists i:exists x:R,(`[l i,r i]:set (real_line_metric R)) x /\ f x=y.
  have /andP[hry hyl]:=hy i.
  have hOrder:f (r i)<=f (l i):=le_trans hry hyl.
  have hBounds:Num.min (f (l i)) (f (r i))<=y<=Num.max (f (l i)) (f (r i)).
    by rewrite min_r // max_l.
  have [x hx hfx]:=@IVT R f (l i) (r i) y (hl i) (continuous_subspaceT hc) hBounds.
  exists x; by split.
pose root:=fun i=>projT1 (cid (hExists i)).
have hRoot i:(`[l i,r i]:set (real_line_metric R)) (root i) /\ f (root i)=y.
  exact (projT2 (cid (hExists i))).
have hMap i:setT i -> mapping_fibre f A y (root i).
  move=>_; split; first exact (hA i _ (hRoot i).1).
  exact (hRoot i).2.
have hInj i j:setT i -> setT j -> root i=root j -> i=j.
  move=>_ _ he; apply/eqP; case:(eqVneq i j)=>// hne; exfalso.
  have hi: l i<=root i<=r i by move:(hRoot i).1; rewrite /= in_itv.
  have hj: l j<=root i<=r j by rewrite he; move:(hRoot j).1; rewrite /= in_itv.
  exact (hd i j hne (root i) hi hj).
have hh:=@counting_measure_injection_bound R [the choiceType of 'I_n]
  [the choiceType of real_line_metric R] setT (mapping_fibre f A y) root hMap hInj.
by rewrite counting_finite_whole card_ord in hh.
Qed.
