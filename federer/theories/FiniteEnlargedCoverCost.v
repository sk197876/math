(** Federer (1969), 2.10.24(2), p. 188: supporting cost bound for one
    enlarged finite layer. The controlled enlargements, rather than the
    original disjoint sets, cover A. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleIndexedCover
  CaratheodoryWeakEnlargementUP NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_enlarged_cover_cost]: supporting
    phi_{k delta}(A)<=k sum zeta(S) for each
    enlarged layer in 2.10.24(2), p. 188.
    Diameter and cost use the common control k;
    Federer's literal hat has diameter control five. *)
Lemma finite_enlarged_cover_cost (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k d : R)
    (nu : set X -> \bar R) (H : {fset set_type F}) (a : set_type F -> R) (A : set X) :
  is_weak_caratheodory_enlargement F c E k ->
  is_metric_scale_envelope (fun j : set_type F=>val j) (fun j=>c (val j)) (k*d)%R%:E nu ->
  (forall j, j \in H -> (a j)%:E=c (val j)) ->
  (forall j, j \in H -> extended_metric_diameter (val j)<=d%:E) ->
  A `<=` \bigcup_(j in [set` H]) E (val j) ->
  nu A<=(k*\sum_(j <- H) a j)%R%:E.
Proof.
move=> hE hn ha hd hcover.
pose J := [the choiceType of set_type F].
pose e (j : J) : J := exist _ (E (val j)) (mem_set (weak_enlargement_member hE (set_valP j))).
have hdiam j (hj : j \in H) : extended_metric_diameter (val (e j))<=(k*d)%R%:E.
  apply: le_trans (weak_enlargement_diameter hE (set_valP j)) _.
  rewrite EFinM; apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW (weak_enlargement_constant_positive hE).
  exact: hd.
have hnon j (hj : j \in H) : 0<=c (val (e j)) := weak_enlargement_cost_nonnegative hE (set_valP (e j)).
have hh := @metric_scale_envelope_indexed_cover R X J J (fun j=>val j) (fun j=>c (val j)) _ nu hn A
  [set` H] e (finite_set_countable (finite_fset H)) hnon hdiam hcover.
apply: le_trans hh _; rewrite big_distrr -sumEFin.
rewrite nonnegative_sum_finite //; rewrite !big_seq; apply: lee_sum=> j hj.
rewrite EFinM (ha j hj).
change (c (E (val j))<=k%:E*c (val j)); exact (@weak_enlargement_cost R X F c E k hE (val j) (set_valP j)).
Qed.
