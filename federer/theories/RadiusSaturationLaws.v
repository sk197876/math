(** The auxiliary class D in Federer (1969), proof of 2.8.10, p. 147: the
    empty family belongs to D, chain unions remain in D, and a sufficiently
    large remaining pair can be adjoined. These consequences use only the
    abstract saturation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_radius_saturated_family]: the printed
    observation that empty belongs to D in Federer 2.8.10,
    p. 147. No eligible pair is required to exist. *)
Lemma empty_radius_saturated_family (R : realType) (X : metricType R)
    (tau : R) (Q : set (X * R)) : is_radius_saturated_family tau Q set0.
Proof.
constructor; [by move=> p []|by move=> p q []|by move=> q p hq []].
Qed.

(** Source for [chain_union_radius_saturated]: every nest
    in D has its union in D, Federer 2.8.10,
    p. 147. The chain may be uncountable or empty. *)
Lemma chain_union_radius_saturated (R : realType) (X : metricType R)
    (tau : R) (Q : set (X * R)) (C : set (set (X * R))) :
  (forall P, C P -> is_radius_saturated_family tau Q P) ->
  (forall P S, C P -> C S -> P `<=` S \/ S `<=` P) ->
  is_radius_saturated_family tau Q (\bigcup_(P in C) P).
Proof.
move=> hs hc; constructor.
- move=> p [P hP hp]; exact (@radius_saturated_members R X tau Q P (hs P hP) p hp).
- move=> p q [P hP hp] [S hS hq] hne.
  have [hPS|hSP] := hc P S hP hS.
  * exact (@radius_saturated_separated R X tau Q S (hs S hS) p q (hPS p hp) hq hne).
  * exact (@radius_saturated_separated R X tau Q P (hs P hP) p q hp (hSP q hq) hne).
- move=> q p hq [P hP hp] hnear.
  have [s [hsp hb]] := @radius_saturated_controls_nearby R X tau Q P (hs P hP)
    q p hq hp hnear.
  exists s; split=> //; by exists P.
Qed.

(** Source for [radius_saturated_insert_large_remaining]:
    the insertion R union {(c,t)} in the last sentence
    of Federer 2.8.10, p. 147. Separation from every
    old pair and a strict radius bound for all remaining
    eligible pairs preserve the defining alternative (3). *)
Lemma radius_saturated_insert_large_remaining (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X * R)) (w : X * R) :
  is_radius_saturated_family tau Q P -> Q w ->
  (forall p, P p -> w.2+p.2 < mdist w.1 p.1) ->
  (forall q, Q q -> (forall p, P p -> q.2+p.2 < mdist q.1 p.1) -> q.2/tau < w.2) ->
  is_radius_saturated_family tau Q (P `|` [set w]).
Proof.
move=> hP hw hsep hlarge; constructor.
- move=> p [hp|->]; last exact hw.
  exact (@radius_saturated_members R X tau Q P hP p hp).
- move=> p q [hp|->] [hq|->] hne.
  * exact (@radius_saturated_separated R X tau Q P hP p q hp hq hne).
  * rewrite addrC metric_sym; exact: hsep.
  * exact: hsep.
  * exfalso; apply: hne; reflexivity.
- move=> q p hq hp hnear.
  case: (pselect (exists t, P t /\ mdist q.1 t.1 <= q.2+t.2))=> [[t [ht hn]]|hn].
  * have [s [hs hb]] := @radius_saturated_controls_nearby R X tau Q P hP q t hq ht hn.
    exists s; split=> //; by left.
  * have hrem t (ht : P t) : q.2+t.2 < mdist q.1 t.1.
      rewrite ltNge; apply/negP=> hle; apply: hn; by exists t.
    have he : p = w.
      case: hp=> [hp|he]; last exact he.
      exfalso; apply: hn; by exists p.
    exists w; split; first by right.
    split; first by rewrite -he.
    exact: hlarge q hq hrem.
Qed.
