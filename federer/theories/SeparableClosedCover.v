(** Federer (1969), 2.2.8, p. 64: countable small-diameter closed covers
    used to build E(s). Intersect a closed parent with small closed balls
    centered in a countable dense set, discard empty intersections, and
    enumerate with repetition. This avoids requiring a chosen dense subset
    of every parent. Source context: MetricClosedBalls.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import MetricClosedBalls CountableFamilyEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_dense_point_near]: supporting density argument for
    Federer 2.2.8, p. 64. *)
Lemma metric_dense_point_near (R : realType) (T : metricType R)
    (D : set T) : dense D -> forall x r, 0 < r ->
  exists c, D c /\ mdist x c < r.
Proof.
move=> hD x r hr.
have hn : [set y | mdist x y < r] !=set0.
  exists x; by rewrite /= mdistxx.
have [c [hc hDc]] := hD _ hn (metric_open_ball_open x r).
exists c; by split.
Qed.

(** Source for [separable_closed_small_cover]: supporting closed-cover
    existence in Federer 2.2.8, p. 64. Every nonempty closed subset of a
    separable metric space is a union of a sequence of nonempty closed
    subsets with diameter at most any prescribed positive e. Finite covers
    are allowed by repetition; no compactness is assumed. *)
Theorem separable_closed_small_cover (R : realType) (T : metricType R)
    (D C : set T) (e : R) : countable D -> dense D -> closed C ->
  C !=set0 -> 0 < e -> exists F : nat -> set T,
    (forall n, closed (F n) /\ F n !=set0 /\ F n `<=` C /\
      forall x y, F n x -> F n y -> mdist x y <= e) /\
    C = \bigcup_n F n.
Proof.
move=> hcnt hD hC [x0 hx0] he.
have he2 : 0 < e/2 by rewrite divr_gt0 // ltr0n.
pose P c := C `&` metric_closed_ball c (e/2).
pose J := [set c | D c /\ P c !=set0].
have hJ : countable J.
  apply: sub_countable _ hcnt; apply: subset_card_le=> c [hc _]; exact hc.
have hcover x : C x -> exists c, J c /\ P c x.
  move=> hx; have [c [hc hnear]] := metric_dense_point_near hD x he2.
  have hp : P c x.
    split=> //; rewrite /metric_closed_ball /= metric_sym; exact: ltW hnear.
  exists c; split=> //; split=> //; by exists x.
have hJn : exists c, J c by have [c [hc _]] := hcover x0 hx0; exists c.
have [F hF] := countable_nonempty_family_enumeration P hJ hJn.
have hmember n : exists c, J c /\ F n = P c.
  have hm : (F @` setT) (F n) by exists n.
  rewrite hF in hm; have [c hc hcF] := hm; exists c; split=> //; exact: esym hcF.
exists F; split.
- move=> n; have [c [[hc hne] ->]] := hmember n.
  split; first exact: (@closedI T C (metric_closed_ball c (e/2)) hC
    (@metric_closed_ball_closed R T c (e/2))).
  split=> //; split; first by move=> x [hx _].
  move=> x y [_ hx] [_ hy].
  have hb := metric_closed_ball_diameter_bound hx hy; by rewrite -splitr in hb.
- apply/seteqP; split.
  + move=> x hx; have [c [hc hp]] := hcover x hx.
    have hm : (P @` J) (P c) by exists c.
    rewrite -hF in hm; have [n _ hn] := hm.
    exists n; first exact Logic.I; by rewrite hn.
  + move=> x [n _ hx]; have [c [_ hn]] := hmember n.
    rewrite hn in hx; exact: hx.1.
Qed.
