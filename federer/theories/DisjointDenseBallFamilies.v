(** Countability step in Federer (1969), 2.8.15, p. 150: disjointed
    positive-radius balls centered on a separable target form a countable
    family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions cardinality reals topology.
From Federer Require Import CountablyClosedFamilyUP CardinalInjection MetricClosedBalls
  MetricSubsetBackground SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [disjoint_family_meeting_countable_set]: the injection
    assigning a dense point to each selected ball in Federer 2.8.15, p. 150
    This supporting set-theoretic lemma applies to arbitrary disjointed sets
    meeting the countable set. No measure or ambient point is required. *)
Lemma disjoint_family_meeting_countable_set (X : choiceType)
    (G : set (set X)) (D : set X) :
  set_family_disjoint G -> countable D ->
  (forall B, G B -> exists x, D x /\ B x) -> countable G.
Proof.
move=> hd hc hmeet.
case: (pselect (exists B, G B))=> [[B0 hB0]|hempty]; last first.
  have he : G = set0.
    apply/seteqP; split=> [B hB|B []]; apply: hempty; by exists B.
  by rewrite he; exact: countable0.
have [x0 _] := hmeet B0 hB0.
have hchoose B : exists x : X, G B -> D x /\ B x.
  case: (pselect (G B))=> [hB|hn].
  - have [x hx] := hmeet B hB; by exists x.
  - exists x0; by move=> /hn.
have [f hf] := choice hchoose.
have hcard : (G #<= D)%card.
  apply: (@cardinal_bound_of_injection [the choiceType of set X] X G D f).
  - move=> B hB; exact: (hf B hB).1.
  - move=> B C hB hC he; apply: contrapT=> hne.
    have hB' := set_mem hB; have hC' := set_mem hC.
    have hh : (B `&` C) (f B).
      split; first exact: (hf B hB').2.
      by rewrite he; exact: (hf C hC').2.
    by rewrite (hd B C hB' hC' hne) in hh.
exact: sub_countable hcard hc.
Qed.

(** Source for [positive_ball_family_centered_on]: the family F' of
    positive-radius balls with centers on A in the proof of Federer 2.8.15,
    p. 150 This supporting family law differs from the existence of a ball
    at every target center: here every family member has such a centered
    representation. No uniform radius bound is needed. *)
Definition positive_ball_family_centered_on (R : realType) (X : metricType R)
    (A : set X) (G : set (set X)) :=
  forall B, G B -> exists a r, A a /\ 0 < r /\ B = metric_closed_ball a r.

(** Source for [separable_centered_disjoint_balls_countable]: Federer
    2.8.15, p. 150, the countability assertion for H_j (paraphrase:
    separability of A makes each selected disjointed family countable).
    Separability is imposed only on the target subspace A. *)
Theorem separable_centered_disjoint_balls_countable (R : realType) (X : metricType R)
    (A : set X) (G : set (set X)) :
  (exists D : set (metric_subset A), countable D /\ dense D) ->
  positive_ball_family_centered_on A G -> set_family_disjoint G -> countable G.
Proof.
move=> [D [hc hd]] hballs hdisj.
pose E : set X := (fun d : metric_subset A => (val d : X)) @` D.
have hE : countable E := sub_countable (card_image_le _ _) hc.
apply: (@disjoint_family_meeting_countable_set X G E hdisj hE).
move=> B hB; have [a [r [ha [hr ->]]]] := hballs B hB.
pose aA : metric_subset A := @exist X (fun x => x \in A) a (mem_set ha).
have [d [hdD hnear]] := @metric_dense_point_near R
  [the metricType R of metric_subset A] D hd aA r hr.
exists (val d); split; first by exists d.
rewrite /metric_closed_ball /=.
change (is_true (mdist a (val d) < r)) in hnear; exact: ltW hnear.
Qed.
