(** Federer (1969), 2.10.24, pp. 186–187:
    supporting regrouping of countable weighted covers.
    Use the numerical-sum laws of 2.1.1(9)–(10),
    p. 53, to exchange row and generator indices.
    No assertion of countable subadditivity of a
    fixed-cutoff weighted infimum is needed. Source
    editions: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction
  NonnegativeSumProduct NonnegativeSumExtendedScale WeightedRepeatedGenerators WeightedMetricEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_dependent_sum_exchange]: supporting
    dependent-family instance of 2.1.1(10), p. 53,
    for the weighted cover choices in 2.10.24,
    pp. 186–187. The outer index domains
    may be uncountable; nonnegativity is explicit. *)
Lemma nonnegative_dependent_sum_exchange (R : realType) (I J : choiceType)
    (G : I -> set J) (f : I -> J -> \bar R) :
  (forall i j, G i j -> 0<=f i j) ->
  nonnegative_sum setT (fun i=>nonnegative_sum (G i) (f i))=
    nonnegative_sum setT (fun j=>nonnegative_sum [set i | G i j] (fun i=>f i j)).
Proof.
move=> hf.
pose P (p : I*J) := if p.2 \in G p.1 then f p.1 p.2 else 0.
have hP p : (setT `*` setT) p -> 0<=P p.
  move=> hp; rewrite /P; case: ifP=> hj; [exact: hf _ _ (set_mem hj)|exact: lexx].
have hrow i : nonnegative_sum setT (fun j=>P (i,j))=nonnegative_sum (G i) (f i).
  by rewrite /P /= nonnegative_sum_restrict setTI.
have hcol j : nonnegative_sum setT (fun i=>P (i,j))=
    nonnegative_sum [set i | G i j] (fun i=>f i j).
  have he : (fun i=>P (i,j))=(fun i=>if i \in [set k | G k j] then f i j else 0).
    apply: funext=> i; rewrite /P /=.
    have hm : (j \in G i)=(i \in [set k | G k j]).
      apply/idP/idP; move=> /set_mem h; exact: mem_set h.
    by rewrite hm.
  by rewrite he nonnegative_sum_restrict setTI.
have h1 := @nonnegative_sum_product_first R I J setT setT P hP.
have h2 := @nonnegative_sum_product_second R I J setT setT P hP.
have heq1 : (fun i=>nonnegative_sum setT (fun j=>P (i,j)))=(fun i=>nonnegative_sum (G i) (f i)).
  apply: funext=> i; exact: hrow i.
have heq2 : (fun j=>nonnegative_sum setT (fun i=>P (i,j)))=
    (fun j=>nonnegative_sum [set i | G i j] (fun i=>f i j)).
  apply: funext=> j; exact: hcol j.
by rewrite heq1 in h1; rewrite heq2 in h2; rewrite -h1 -h2.
Qed.

(** Source for [weighted_cover_cost_reindexing]: supporting
    regrouping of weighted covering costs in
    2.10.24, pp. 186–187. The equality
    permits infinite weights at this intermediate stage;
    they are removed or proved finite before
    constructing a cover with the printed real weights. *)
Theorem weighted_cover_cost_reindexing (R : realType) (J : choiceType)
    (G : nat -> set J) (a : nat -> J -> R) (c : J -> \bar R) :
  (forall n j, G n j -> (0<=a n j)%R) -> (forall j, 0<=c j) ->
  nonnegative_sum setT (fun n=>weighted_generator_cost c (G n) (a n))=
    nonnegative_sum setT (fun j=>repeated_generator_weight G a j*c j).
Proof.
move=> ha hc; rewrite /weighted_generator_cost nonnegative_dependent_sum_exchange.
- apply: nonnegative_sum_ext=> j _.
  have he : nonnegative_sum [set n | G n j] (fun n=>(a n j)%:E*c j)=
      nonnegative_sum [set n | G n j] (fun n=>c j*(a n j)%:E).
    apply: nonnegative_sum_ext=> n hn; exact: muleC.
  rewrite he nonnegative_sum_extended_scale; [exact: muleC|exact: hc|].
  by move=> n hn; rewrite lee_fin; exact: ha n j hn.
- move=> n j hj; apply: mule_ge0; [by rewrite lee_fin; exact: ha n j hj|exact: hc].
Qed.

(** Source for [weighted_cover_point_reindexing]: supporting
    pointwise regrouping of the weighted sums in
    2.10.24, p. 186. A source generator
    contributes at x exactly when it contains x. *)
Theorem weighted_cover_point_reindexing (R : realType) (X J : choiceType)
    (S : J -> set X) (G : nat -> set J) (a : nat -> J -> R) x :
  (forall n j, G n j -> (0<=a n j)%R) ->
  nonnegative_sum setT (fun n=>weighted_generator_sum S (G n) (a n) x)=
    nonnegative_sum [set j | S j x] (fun j=>repeated_generator_weight G a j).
Proof.
move=> ha; rewrite /weighted_generator_sum nonnegative_dependent_sum_exchange.
- have he : (fun j=>nonnegative_sum [set n | G n j /\ S j x] (fun n=>(a n j)%:E))=
      (fun j=>if j \in [set k | S k x] then repeated_generator_weight G a j else 0).
    apply: funext=> j; case: ifP=> hj.
    + have hS : S j x := set_mem hj.
      have heq : [set n | G n j /\ S j x]=[set n | G n j].
        apply/seteqP; split=> [n [hn _]|n hn] //; by split.
      by rewrite heq.
    + have hnot : ~S j x.
        move=> hS; have hmem : j \in [set k | S k x] by apply: mem_set; exact hS.
        by move: hj; rewrite hmem.
      have heq : [set n | G n j /\ S j x]=(@set0 nat).
        apply/seteqP; split=> [n [hn hS]|n []]; exact: False_ind _ (hnot hS).
      by rewrite heq nonnegative_sum_empty.
  by rewrite he nonnegative_sum_restrict setTI.
- move=> n j [hj _]; rewrite lee_fin; exact: ha n j hj.
Qed.
