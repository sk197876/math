(** General topology supporting Federer (1969), 2.2.10, p. 65: the nonempty
    closed witness C in a separable metric space is separable. At each
    shrinking scale take the countable small closed cover already proved for
    2.2.8, and select one point in each cover member. This is a supporting
    proof of the stated background fact, not a separability hypothesis
    imposed on the final result. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricSubsetBackground SeparableClosedCover
  ClosedCoverTreeUP ClosedCoverBranches.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonempty_closed_metric_subset_separable]: supporting
    separability of C in Federer 2.2.10, p. 65. The countable family of
    selected points meets every relative ball, because cover diameters tend
    to zero. *)
Theorem nonempty_closed_metric_subset_separable (R : realType) (T : metricType R)
    (A : set T) :
  (exists D : set T, countable D /\ dense D) -> closed A -> A !=set0 ->
  exists H : set (metric_subset A), countable H /\ dense H.
Proof.
move=> [D [hc hd]] hA hn.
have hex k := @separable_closed_small_cover R T D A (@closed_cover_tree_scale R k)
  hc hd hA hn (@closed_cover_tree_scale_positive R k).
pose C k := projT1 (cid (hex k)).
have hC k := projT2 (cid (hex k)).
have hp k i : C k i !=set0 := ((hC k).1 i).2.1.
pose p k i := projT1 (cid (hp k i)).
have hpin k i : C k i (p k i) := projT2 (cid (hp k i)).
have hpA k i : A (p k i) := ((hC k).1 i).2.2.1 _ (hpin k i).
pose q (ki : nat * nat) : metric_subset A :=
  @exist T (fun x => x \in A) (p ki.1 ki.2) (mem_set (hpA ki.1 ki.2)).
exists (q @` setT); split.
- apply: sub_countable (card_image_le _ _) _; exact: countableP.
- move=> W [x hx] ho.
  have hnb : nbhs x W by rewrite openE in ho; exact: ho x hx.
  have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hnb.
  have [k0 hk] := closed_cover_tree_scale_small he.
  pose k := k0.+1.
  have hv : A (val x) := set_valP x.
  have hv' : (\bigcup_i C k i) (val x).
    have heq := congr1 (fun B : set T => B (val x)) (hC k).2.
    by rewrite -heq.
  have [i _ hi] := hv'.
  exists (q (k,i)); split; last by exists (k,i).
  apply: hb; change (mdist (val x) (p k i) < e).
  apply: le_lt_trans _ hk; exact: ((hC k).1 i).2.2.2 _ _ hi (hpin k i).
Qed.
