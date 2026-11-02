(** Federer (1969), 2.9.20, pp. 165–166: continuity on the closed segment is
    global continuity at its interior points, but only one-sided continuity
    is available at its endpoints. These are general order-topology
    supporting facts; no global endpoint continuity is added. Source
    editions: RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [segment_continuity_interior]: supporting use of continuity
    in the implication (4)=>(1) of Federer 2.9.20, p. 166 At an interior
    point the closed segment is a neighbourhood, so relative and ambient
    continuity agree. The endpoints are deliberately excluded. *)
Lemma segment_continuity_interior (R : realType) (g : R -> R) (a b x : R) :
  {within (`[a,b] : set (real_line_metric R)),
    continuous (g : real_line_metric R -> real_line_metric R)} ->
  a<x -> x<b -> (g : real_line_metric R -> real_line_metric R) @
    (x : real_line_metric R) --> (g x : real_line_metric R).
Proof.
move=> hc hax hxb.
have hx : (`[a,b] : set (real_line_metric R)) x.
  by rewrite /= in_itv /= (ltW hax) (ltW hxb).
have hnearOpen : nbhs (x : real_line_metric R) `]a,b[.
  apply: open_nbhs_nbhs; split; first exact: interval_open.
  by rewrite /= in_itv /= hax hxb.
have hnear : nbhs (x : real_line_metric R) `[a,b].
  apply: (filterS _ hnearOpen)=> y.
  rewrite /= !in_itv /= => /andP[hay hyb].
  by rewrite (ltW hay) (ltW hyb).
have hcx := (subspace_continuousP _ _).1 hc x hx.
by rewrite (within_interior hnear) in hcx.
Qed.

(** Source for [half_open_interval_inside_open_bounds]: supporting endpoint
    bounds for the open-set argument in Federer 2.9.20, p. 166 A nonempty
    half-open interval contained in (a,b) has its left endpoint strictly
    inside (a,b), and its excluded right endpoint is at most b. This is an
    order fact, not a new measure claim. *)
Lemma half_open_interval_inside_open_bounds (R : realType) (a b u v : R) :
  u<v -> (`[u,v[ : set R) `<=` `]a,b[ -> a<u /\ v<=b.
Proof.
move=> huv hs.
have hu : (`[u,v[ : set R) u by rewrite /= in_itv /= lexx huv.
have hau : a<u.
  by have := hs u hu; rewrite /= in_itv /= => /andP[].
split=> //; rewrite leNgt; apply/negP=> hbv.
have hmax : Num.max u b<v by rewrite gt_max huv hbv.
have [hleft hright] := midf_lt hmax.
pose x := (Num.max u b+v)/2.
have hum : u<=Num.max u b by rewrite le_max lexx.
have hbm : b<=Num.max u b by rewrite le_max lexx orbT.
have hux : u<x := le_lt_trans hum hleft.
have hbx : b<x := le_lt_trans hbm hleft.
have hx : (`[u,v[ : set R) x by rewrite /= in_itv /= (ltW hux) hright.
have hxb : x<b by have := hs x hx; rewrite /= in_itv /= => /andP[].
by have := lt_trans hbx hxb; rewrite ltxx.
Qed.
