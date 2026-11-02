(** Federer (1969), 2.10.24, pp. 186–188: scalar weight identities used in
    the weighted upper-integral comparison and rational-to-integer weight
    reduction. These follow from the project's abstract nonnegative-sum laws
    of 2.1.1(6), p. 52. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumScale WeightedMetricEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_generator_sum_scale]: supporting
    scaling of the pointwise weighted sum in
    2.10.24, pp. 186–188. A zero scalar
    is included with zero times infinity zero. *)
Lemma weighted_generator_sum_scale (R : realType) (X J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) (t : R) x :
  (0<=t)%R -> (forall j, G j -> (0<=u j)%R) ->
  weighted_generator_sum S G (fun j=>(t*u j)%R) x=t%:E*weighted_generator_sum S G u x.
Proof.
move=> ht hu; rewrite /weighted_generator_sum.
have he : (fun j=>((t*u j)%R)%:E)=(fun j=>t%:E*(u j)%:E).
  apply: funext=> j; exact: EFinM.
rewrite he nonnegative_sum_scale //.
by move=> j [hj _]; rewrite lee_fin; exact: hu.
Qed.

(** Source for [weighted_generator_cost_scale]: supporting
    scaling of the weighted covering cost in
    2.10.24, pp. 186–188. No finite-cost
    assumption is needed for this nonnegative identity. *)
Lemma weighted_generator_cost_scale (R : realType) (J : choiceType)
    (c : J -> \bar R) (G : set J) (u : J -> R) (t : R) :
  (0<=t)%R -> (forall j, G j -> (0<=u j)%R) -> (forall j, G j -> 0<=c j) ->
  weighted_generator_cost c G (fun j=>(t*u j)%R)=t%:E*weighted_generator_cost c G u.
Proof.
move=> ht hu hc; rewrite /weighted_generator_cost.
have he : (fun j=>((t*u j)%R)%:E*c j)=(fun j=>t%:E*((u j)%:E*c j)).
  apply: funext=> j; by rewrite EFinM muleA.
rewrite he nonnegative_sum_scale //.
move=> j hj; apply: mule_ge0; [by rewrite lee_fin; exact: hu|exact: hc].
Qed.

(** Source for [weighted_generator_sum_member_bound]: supporting
    single-generator contribution in the weighted
    pointwise domination condition of 2.10.24,
    p. 186. *)
Lemma weighted_generator_sum_member_bound (R : realType) (X J : choiceType)
    (S : J -> set X) (G : set J) (u : J -> R) j x :
  G j -> S j x -> (u j)%:E<=weighted_generator_sum S G u x.
Proof. move=> hj hx; apply: nonnegative_sum_term; by split. Qed.
