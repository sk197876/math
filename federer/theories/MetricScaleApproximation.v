(** Federer (1969), 2.10.1, p. 170: choose a countable admissible cover with
    cost below any strict upper bound on the approximating infimum. The same
    choice supports the open-refinement characterisation, whose corrected
    reference is Federer1955 Theorem 2.5, pp. 291–292 (local erratum p. 3,
    book p. 170 lines 24 and 35). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MetricDiameter MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_scale_envelope_approximation]: supporting cover
    choice for the infimum in Federer 2.10.1, p. 170 Unlike an attained
    minimum, this only requires a strict upper bound. Infinity and empty or
    nonexistent admissible covers retain their original order-theoretic
    meanings. *)
Lemma metric_scale_envelope_approximation (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    (delta : \bar R) (nu : set X -> \bar R) (A : set X) (b : \bar R) :
  is_metric_scale_envelope S cost delta nu -> nu A<b ->
  exists G : set J, countable G /\
    (forall j, G j -> extended_metric_diameter (S j)<=delta) /\
    A `<=` \bigcup_(j in G) S j /\ nonnegative_sum G cost<b.
Proof.
move=> hn hb; apply: contrapT=> hnone.
have hle : b<=nu A.
  apply: (metric_scale_envelope_greatest hn)=> G hc hd hcov.
  rewrite leNgt; apply/negP=> hlt; apply: hnone.
  exists G; by split=> //; split=> //; split.
by have := lt_le_trans hb hle; rewrite ltxx.
Qed.
