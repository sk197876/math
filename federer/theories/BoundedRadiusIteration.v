(** Termination argument in Federer (1969), 2.8.12, p. 149: a remaining pair
    would have distinct nearby selected witnesses from 2 zeta+1 stages,
    contradicting 2.8.11. The proof uses only abstract iteration and
    controlled family laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import DirectionalLimitationUP DirectionalCoverCardinality
  RadiusCoverSelectionUP RadiusSelectionIterationUP RadiusSelectionIterationLaws
  DistinguishedFiniteFamily SmallRadiusNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [controlled_ball_family_subset]: the finite
    family P of witnesses is controlled because it is a subset
    of Q, Federer 2.8.12, p. 149. Supporting inheritance law. *)
Lemma controlled_ball_family_subset (R : realType) (X : metricType R)
    (tau : R) (Q P : set (X*R)) :
  is_controlled_ball_family tau Q -> P `<=` Q -> is_controlled_ball_family tau P.
Proof.
move=> hQ hPQ; constructor.
- exact: controlled_factor_gt_one hQ.
- move=> p hp; exact (@controlled_positive_radii R X tau Q hQ p (hPQ p hp)).
- move=> p q hp hq hne.
  exact (@controlled_pair_alternative R X tau Q hQ p q (hPQ p hp) (hPQ q hq) hne).
Qed.

(** Source for [radius_selection_iteration_finishes]: emptiness
    of Q_(2 zeta+2) in Federer 2.8.12, p. 149. In the
    zero-based formal indexing this is W(2 zeta+1). Every
    hypothetical survivor supplies too many distinct controlled
    parameters near itself, contradicting the cardinal bound. *)
Theorem radius_selection_iteration_finishes (R : realType) (X : metricType R)
    (A : set X) (xi : \bar R) (eta tau mu : R) (zeta : nat)
    (Q : set (X*R)) (W S : nat -> set (X*R)) :
  is_directionally_limited_at A xi eta zeta ->
  has_directional_cover_factor eta tau -> is_controlled_ball_family tau Q ->
  (forall p, Q p -> A p.1) -> is_bounded_positive_radius_family mu Q ->
  (mu%:E < (1/2 : R)%:E * xi)%E ->
  is_radius_selection_iteration tau Q W S -> W (2*zeta+1)%N = set0.
Proof.
move=> hlim hfactor hQ hA hbounded hsmall hiter.
pose N := (2*zeta+1)%N.
apply/seteqP; split=> [p hp|p []]; exfalso.
have hpQ := @radius_iteration_remainder_subset R X tau Q W S hiter N p hp.
have hex (i : 'I_N) : exists q,
    S i q /\ mdist p.1 q.1 <= p.2+q.2 /\ p.2/tau < q.2.
  have hin : W i p := @radius_iteration_decreasing R X tau Q W S hiter
    i N (ltnW (valP i)) p hp.
  exact (@radius_selection_dominates R X tau (W i) (S i)
    (@radius_iteration_selection R X tau Q W S hiter i) p hin).
have [b hb] := choice hex.
have hbinj : injective b.
  move=> i j he; apply: contrapT=> hne.
  have hvals : (i : nat) <> (j : nat) by move=> hij; apply: hne; exact: val_inj hij.
  apply: (@radius_iteration_distinct_stages R X tau Q W S hiter i j hvals
    (b i) (hb i).1).
  by rewrite he; exact: (hb j).1.
have hbp (i : 'I_N) : b i <> p.
  move=> he; apply: (@radius_iteration_later_avoids_selection R X tau Q W S hiter
    i N (valP i) p hp).
  by rewrite -he; exact: (hb i).1.
pose P : set (X*R) := [set p] `|` (b @` setT).
have hPQ : P `<=` Q.
  move=> q [->|[i _ <-]]; first exact hpQ.
  exact (@radius_iteration_selected_subset R X tau Q W S hiter i (b i) (hb i).1).
have hP : is_controlled_ball_family tau P := controlled_ball_family_subset hQ hPQ.
have hpP : P p by left.
have hAP q : P q -> A q.1 by move=> hq; exact: hA q (hPQ q hq).
have ht := controlled_factor_gt_one hQ.
have ht0 := lt_trans ltr01 ht.
have hr := @controlled_positive_radii R X tau Q hQ p hpQ.
have hself : p.2/tau < p.2 by rewrite ltr_pdivrMr // ltr_pMr.
have hlocal q : P q ->
    ((mdist p.1 q.1)%:E < xi)%E /\ mdist p.1 q.1 <= p.2+q.2 /\ p.2/tau < q.2.
  move=> [->|[i _ <-]].
  - split; first by rewrite mdistxx; exact: directional_radius_positive hlim.
    split=> //; by rewrite mdistxx addr_ge0 ?ltW.
  - have hbQ : Q (b i).
      apply: hPQ; right; by exists i.
    split; last exact: (hb i).2.
    exact (@small_radii_meeting_center_near R X xi mu Q hbounded hsmall
      p (b i) hpQ hbQ (hb i).2.1).
have hbound := @federer_2_8_11 R X A xi eta tau zeta P p hlim hfactor hP hpP hAP hlocal.
exact: (@distinguished_finite_family_exceeds_bound [the choiceType of (X*R)%type]
  N p b hbinj hbp hbound).
Qed.
