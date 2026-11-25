(** Federer (1969), 2.2.15, p. 71, final target criterion: private
    countable-range approximation of a Borel map into a nonempty separable
    metric target. Enumerate a dense set and select the first ball of radius
    1/(k+1) containing the value. The abstract Borel-cover index hides the
    natural least-index construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricClosedBalls SeparableClosedCover TopologicalBorel BorelFunctionUP
  BorelDiscreteIndexUP BorelCoverIndexSealed CountableBorelApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_nonempty_point_enumeration]: supporting
    set-theoretic enumeration for Federer 2.2.15, p. 71.
    Missing natural codes repeat a fixed member, preserving
    finite and infinite nonempty sets without adding values. *)
Lemma countable_nonempty_point_enumeration (Y : choiceType) (D : set Y) :
  countable D -> D !=set0 -> exists y : nat -> Y, y @` setT = D.
Proof.
move=> /countable_injP[g hg] [y0 hy0].
have hc n : exists y, D y /\ forall z, D z -> g z = n -> y = z.
  case: (pselect (exists y, D y /\ g y = n))=> [[y [hy he]]|hn].
  - exists y; split=> // z hz hez; apply: hg.
    + exact: mem_set hy.
    + exact: mem_set hz.
    + by rewrite he hez.
  - exists y0; split=> // z hz hez; exfalso; apply: hn; exists z; by split.
pose y n := projT1 (cid (hc n)).
have hy n := projT2 (cid (hc n)).
exists y; apply/seteqP; split.
- move=> z [n _ <-]; exact: (hy n).1.
- move=> z hz; exists (g z); first exact Logic.I.
  exact: (hy (g z)).2 z hz (erefl _).
Qed.

(** Source for [countable_borel_approximation_exists]: supporting
    existence proof for the sufficiency of Federer 2.2.15,
    p. 71. Separability supplies a dense sequence; Borel
    preimages of its open balls supply Borel step labels. *)
Theorem countable_borel_approximation_exists (R : realType) (X : topologicalType)
    (Y : metricType R) (f : X -> Y) (y0 : Y) (D : set Y) :
  countable D -> dense D -> is_borel_function f ->
  exists y, exists q, is_countable_borel_approximation f y q.
Proof.
move=> hc hd hf.
have hDn : D !=set0.
  have [z [hz _]] := metric_dense_point_near hd y0 (@ltr01 R); by exists z.
have [y hy] := countable_nonempty_point_enumeration hc hDn.
pose A k n := f @^-1` [set z | mdist (y n) z < ((k.+1)%:R)^-1].
have hA k n : borel_set (A k n).
  apply: hf; exact: metric_open_ball_open.
have hcover k x : exists n, A k n x.
  have he : (0 : R) < ((k.+1)%:R)^-1 by rewrite invr_gt0 ltr0n.
  have [z [hz hdist]] := metric_dense_point_near hd (f x) he.
  rewrite -hy in hz; have [n _ hn] := hz.
  exists n; rewrite /A /= metric_sym hn; exact hdist.
pose q k := @BorelCoverIndex.value X (A k) (hA k) (hcover k).
have hq k := @BorelCoverIndex.laws X (A k) (hA k) (hcover k).
exists y, q; constructor.
- move=> k; exact: first_borel_cover_fibres (hq k).
- move=> k x; have hh := first_borel_cover_hit (hq k) x.
  change (is_true (mdist (y (q k x)) (f x) < ((k.+1)%:R)^-1)) in hh.
  by rewrite metric_sym.
Qed.
