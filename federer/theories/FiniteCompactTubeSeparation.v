(** Federer (1969), 3.2.37, p. 274: finitely many disjoint
    compact source pieces have pairwise disjoint sufficiently small
    tubes. This is the finite-additivity step before taking liminf. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import MetricOpenThickening CompactDisjointLipschitzUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_compact_open_tubes_separated]: the uniform
    small-radius disjointness used for the compact-family bound in
    Federer 3.2.37, p. 274. The index family, any of its pieces
    and the ambient metric space may have degenerate size. *)
Lemma finite_compact_open_tubes_separated (R:realType) (X:metricType R)
    (I:choiceType) (B:{fset I}) (K:I->set X):
  (forall i,i \in B ->compact (K i)) ->
  (forall i j,i \in B ->j \in B ->i!=j ->forall x,K i x ->K j x ->False) ->
  exists e:R,0<e /\ forall r:R,0<r<e ->
    forall i j,i \in B ->j \in B ->i!=j ->forall x,
      metric_open_thickening (K i) r x ->metric_open_thickening (K j) r x ->False.
Proof.
move=>hK hDisjoint.
have hPair (u v:B):exists d:R,0<d /\
    (val u!=val v ->forall x y,K (val u) x ->K (val v) y ->d<=mdist x y).
  case:(pselect (val u=val v))=>hEqual.
  - exists 1; split; first exact:ltr01.
    move=>hNe; exfalso; by move:hNe; rewrite hEqual eqxx.
  - have hDifferent:(val u!=val v) by apply/eqP.
    have [d [hd hSeparated]]:=compact_disjoint_metric_separation
      (hK (val u) (fsvalP u))
      (compact_closed (@metric_hausdorff R X) (hK (val v) (fsvalP v)))
      (hDisjoint (val u) (val v) (fsvalP u) (fsvalP v) hDifferent).
    exists d; split=>// _; exact:hSeparated.
pose d (p:B*B):=projT1 (cid (hPair p.1 p.2)).
have hD (p:B*B):0<d p /\
    (val p.1!=val p.2 ->forall x y,K (val p.1) x ->K (val p.2) y ->d p<=mdist x y).
  exact:projT2 (cid (hPair p.1 p.2)).
pose delta:=\big[Order.min/1]_(p:B*B) d p.
have hDelta:0<delta.
  rewrite /delta; apply:(big_ind (fun t:R=>0<t)); first exact:ltr01.
  - by move=>a b ha hb; rewrite lt_min ha hb.
  - move=>p _; exact:(hD p).1.
exists (delta/3); split; first by rewrite divr_gt0 // ltr0n.
move=>r /andP[hr hrDelta] i j hi hj hij x [a ha hax] [b hb hbx].
pose p:B*B:=([` hi],[` hj]).
have hMin:=bigmin_le (1:R) p d.
have hPoints:delta<=mdist a b:=le_trans hMin ((hD p).2 hij a b ha hb).
have hTriangle:=metric_triangle a x b.
rewrite (metric_sym x b) in hTriangle.
change (is_true (mdist a x<r)) in hax.
change (is_true (mdist b x<r)) in hbx.
have hBad:delta<delta by lra.
by rewrite ltxx in hBad.
Qed.
