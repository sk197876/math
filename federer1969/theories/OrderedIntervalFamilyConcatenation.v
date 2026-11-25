(** Supporting finite refinements in Federer (1969), 2.9.20, p. 166, first
    consequent implication of (3). Concatenation preserves the abstract
    family laws; numerical length and increment sums add. Source context and
    conventions: OrderedIntervalFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import OrderedIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ordered_real_interval_family_cat]: supporting ordered
    concatenation for the refined families in Federer 2.9.20, p. 166 Empty
    component families and shared endpoints are permitted. *)
Lemma ordered_real_interval_family_cat (R : realType) (a c b : R)
    (s t : seq (R * R)) : a<=c -> c<=b ->
  is_ordered_real_interval_family a c s ->
  is_ordered_real_interval_family c b t ->
  is_ordered_real_interval_family a b (s++t).
Proof.
move=> hac hcb hs ht; elim: s a hac hs=> [|[u v] s ih] a hac /= hs.
- exact: ordered_real_interval_family_lower_bound hac ht.
- have [hau [huv [hvc hs']]] := hs.
  split=> //; split=> //; split; first exact: le_trans hvc hcb.
  exact: ih hvc hs'.
Qed.

(** Source for [real_interval_family_length_cat]: supporting additivity
    of the length sum under refinement in Federer 2.9.20, p. 166. *)
Lemma real_interval_family_length_cat (R : realType) (s t : seq (R * R)) :
  real_interval_family_length (s++t)=
    real_interval_family_length s+real_interval_family_length t.
Proof. by rewrite /real_interval_family_length big_cat. Qed.

(** Source for [real_interval_family_increment_sum_cat]: supporting
    additivity of the increment sum under refinement in Federer
    2.9.20, p. 166. No ordering or regularity hypothesis is needed. *)
Lemma real_interval_family_increment_sum_cat (R : realType) (g : R -> R)
    (s t : seq (R * R)) : real_interval_family_increment_sum g (s++t)=
    real_interval_family_increment_sum g s+real_interval_family_increment_sum g t.
Proof. by rewrite /real_interval_family_increment_sum big_cat. Qed.
