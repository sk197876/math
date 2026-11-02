(** Chain-union and insertion laws for the class D in Federer (1969), proof
    of 2.8.13, pp. 149–150. its relaxed inequalities are not transferred.
    The proofs use only the abstract controlledness and saturation laws.
    Source context: ControlledCenterSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import DirectionalLimitationUP ControlledCenterSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_center_saturated_family]: empty belongs to the
    maximal-principle class in Federer 2.8.13, p. 149 Tau>1 remains a law of
    controlledness even for the empty selected family. *)
Lemma empty_center_saturated_family (R : realType) (X : metricType R)
    (tau : R) (Q : set (X*R)) : 1 < tau -> is_center_saturated_family tau Q set0.
Proof.
move=> ht; constructor.
- by move=> p [].
- constructor.
  + exact ht.
  + by move=> p [].
  + by move=> p q [].
- move=> q hq; right; by move=> p [].
Qed.

(** Source for [chain_union_center_saturated]: the union of a nest remains
    in the class D of Federer 2.8.13, p. 149. Empty nests and arbitrary
    cardinality are permitted. *)
Lemma chain_union_center_saturated (R : realType) (X : metricType R)
    (tau : R) (Q : set (X*R)) (C : set (set (X*R))) :
  1 < tau -> (forall P, C P -> is_center_saturated_family tau Q P) ->
  (forall P S, C P -> C S -> P `<=` S \/ S `<=` P) ->
  is_center_saturated_family tau Q (\bigcup_(P in C) P).
Proof.
move=> ht hs hc; constructor.
- move=> p [P hP hp]; exact (@center_saturated_members R X tau Q P (hs P hP) p hp).
- constructor=> //.
  + move=> p [P hP hp].
    exact (@controlled_positive_radii R X tau P (center_saturated_controlled (hs P hP)) p hp).
  + move=> p q [P hP hp] [S hS hq] hne.
    have [hPS|hSP] := hc P S hP hS.
    * exact (@controlled_pair_alternative R X tau S (center_saturated_controlled (hs S hS))
        p q (hPS p hp) hq hne).
    * exact (@controlled_pair_alternative R X tau P (center_saturated_controlled (hs P hP))
        p q hp (hSP q hq) hne).
- move=> q hq.
  case: (pselect (exists p, (\bigcup_(P in C) P) p /\ mdist p.1 q.1 <= p.2))=> [he|hn]; first by left.
  right=> p [P hP hp].
  have [[s [hsp hcov]]|hsep] := @center_saturated_alternative R X tau Q P (hs P hP) q hq.
  * exfalso; apply: hn; exists s; split=> //; by exists P.
  * exact: hsep p hp.
Qed.

(** Source for [center_saturated_insert_large_remaining]: adjoin (c,t) with
    tau t above all uncovered radii in Federer 2.8.13, p. 150 The old
    alternative gives controlledness with old pairs; the strict large-radius
    choice gives the new alternative. *)
Lemma center_saturated_insert_large_remaining (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X*R)) (w : X*R) :
  is_center_saturated_family tau Q P -> Q w -> 0 < w.2 ->
  (forall p, P p -> p.2 < mdist p.1 w.1) ->
  (forall q, Q q -> (forall p, P p -> p.2 < mdist p.1 q.1) -> q.2/tau < w.2) ->
  is_center_saturated_family tau Q (P `|` [set w]).
Proof.
move=> hP hw hwpos huncovered hlarge.
have hold p : P p -> p.2 < mdist p.1 w.1 /\ w.2/tau < p.2.
  move=> hp.
  have [[q [hq hcov]]|hsep] := @center_saturated_alternative R X tau Q P hP w hw.
  - by have := lt_le_trans (huncovered q hq) hcov; rewrite ltxx.
  - exact: hsep p hp.
constructor.
- move=> p [hp|->]; last exact hw.
  exact (@center_saturated_members R X tau Q P hP p hp).
- constructor.
  + exact: controlled_factor_gt_one (center_saturated_controlled hP).
  + move=> p [hp|->]; last exact hwpos.
    exact (@controlled_positive_radii R X tau P (center_saturated_controlled hP) p hp).
  + move=> p q [hp|->] [hq|->] hne.
    * exact (@controlled_pair_alternative R X tau P (center_saturated_controlled hP) p q hp hq hne).
    * left; exact: hold p hp.
    * right; rewrite metric_sym; exact: hold q hq.
    * exfalso; apply: hne; reflexivity.
- move=> q hq.
  case: (pselect (exists p, (P `|` [set w]) p /\ mdist p.1 q.1 <= p.2))=> [he|hn]; first by left.
  have hrem p : P p -> p.2 < mdist p.1 q.1.
    move=> hp; rewrite ltNge; apply/negP=> hcov; apply: hn.
    exists p; split=> //; by left.
  right=> p [hp|->].
  + have [[s [hsp hcov]]|hsep] := @center_saturated_alternative R X tau Q P hP q hq.
    * exfalso; apply: hn; exists s; split=> //; by left.
    * exact: hsep p hp.
  + split; last exact: hlarge q hq hrem.
    rewrite ltNge; apply/negP=> hcov; apply: hn.
    exists w; split=> //; by right.
Qed.
