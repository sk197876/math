(** Federer (1969), 2.10.24(2), p. 188: supporting finite forms of the
    weighted generator point sums and costs. They identify the project's
    abstract nonnegative sum with finite real addition, by 2.1.1(3), p. 52.
    Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction WeightedMetricEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_weighted_generator_point_sum]: supporting
    finite real point sum in the reduction of
    2.10.24(2), p. 188. Nonnegative finite weights
    ensure agreement with the abstract extended sum. *)
Lemma finite_weighted_generator_point_sum (R : realType) (X J : choiceType)
    (S : J -> set X) (P : {fset J}) (v : J -> R) x :
  (forall j, j \in P -> (0<=v j)%R) ->
  weighted_generator_sum S [set` P] v x=
    (\sum_(j <- P) (if x \in S j then v j else 0))%R%:E.
Proof.
move=> hv; rewrite /weighted_generator_sum -nonnegative_sum_restrict.
have he : (fun j : J=>if j \in [set j | S j x] then (v j)%:E else 0)=
    (fun j=>(if x \in S j then v j else 0)%R%:E).
  apply: funext=> j.
  have hi : (j \in [set j | S j x])=(x \in S j).
    apply/idP/idP=> /set_mem hx; apply: mem_set; exact hx.
  rewrite hi; by case: ifP.
rewrite he nonnegative_sum_finite //; first by rewrite sumEFin.
move=> j hj; case: ifP=> _; rewrite lee_fin; [exact: hv|exact: lexx].
Qed.

(** Source for [finite_weighted_generator_cost]: supporting
    finite cost sum for the last estimate in
    2.10.24(2), p. 188. Costs are presented
    by their finite real representatives in this lemma. *)
Lemma finite_weighted_generator_cost (R : realType) (J : choiceType)
    (P : {fset J}) (v c : J -> R) :
  (forall j, j \in P -> (0<=v j)%R) -> (forall j, j \in P -> (0<=c j)%R) ->
  weighted_generator_cost (fun j=>(c j)%:E) [set` P] v=
    (\sum_(j <- P) v j*c j)%R%:E.
Proof.
move=> hv hc; rewrite /weighted_generator_cost nonnegative_sum_finite.
- rewrite -sumEFin; apply: eq_big_seq=> j hj; by rewrite EFinM.
- move=> j hj; apply: mule_ge0; rewrite lee_fin; [exact: hv|exact: hc].
Qed.
