(** Federer (1969), 3.1.13, p. 224:
    disjoint positive-radius balls in Euclidean
    space have a countable set of centers.
    The supporting statement applies to any
    metric space with a countable dense subset. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import MetricClosedBalls CountablyClosedFamilyUP CardinalInjection
  DisjointDenseBallFamilies SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separable_disjoint_ball_centers_countable]:
    the assertion that S is countable in
    Federer 3.1.13, p. 224. A
    countable dense set meets every positive
    ball; disjointness makes the association
    injective, also at the level of centers. *)
Theorem separable_disjoint_ball_centers_countable (R : realType) (X : metricType R)
    (S : set X) (h : X->R) :
  (exists D : set X, countable D /\ dense D) ->
  (forall s, S s -> 0<h s) ->
  (forall s t, S s -> S t -> s<>t ->
    metric_closed_ball s (h s) `&` metric_closed_ball t (h t)=set0) ->
  countable S.
Proof.
move=>[D [hDc hDd]] hp hdis.
pose ball s := metric_closed_ball s (h s).
pose G := ball @` S.
have hGdis : set_family_disjoint G.
  move=>B C [s hs <-] [t ht <-] hne.
  have hst : s<>t by move=>he; apply: hne; by rewrite he.
  exact: hdis s t hs ht hst.
have hmeet B : G B -> exists d, D d /\ B d.
  move=>[s hs <-].
  have [d [hd hnear]] := @metric_dense_point_near R X D hDd s (h s) (hp s hs).
  exists d; split; first exact hd.
  exact: ltW hnear.
have hGc := disjoint_family_meeting_countable_set hGdis hDc hmeet.
have hcard : (S #<= G)%card.
  apply: (@cardinal_bound_of_injection X [the choiceType of set X] S G ball).
  - move=>s hs; by exists s.
  - move=>s t hs ht he; apply: contrapT=>hne.
    have hss := set_mem hs; have htt := set_mem ht.
    have hsball : ball s s.
      rewrite /ball /metric_closed_ball /= mdistxx; exact: ltW (hp s hss).
    have hboth : (ball s `&` ball t) s.
      split; first exact hsball; by rewrite -he.
    by rewrite (hdis s t hss htt hne) in hboth.
exact: sub_countable hcard hGc.
Qed.
