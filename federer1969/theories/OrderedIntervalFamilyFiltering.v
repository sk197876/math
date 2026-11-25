(** Supporting finite disjoint families in Federer (1969), 2.9.20, p. 166.
    Taking a subfamily preserves order, and membership bounds determine the
    ambient interval. Source context and strict-cell convention:
    OrderedIntervalFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import OrderedIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [ordered_real_interval_family_filter]: supporting subfamily
    law for the finite families in Federer 2.9.20, p. 166 Removing cells
    retains their original order and endpoint bounds. *)
Lemma ordered_real_interval_family_filter (R : realType) (a b : R)
    (s : seq (R * R)) (P : pred (R * R)) :
  is_ordered_real_interval_family a b s ->
  is_ordered_real_interval_family a b [seq uv <- s | P uv].
Proof.
elim: s a=> [//|[u v] s ih] a /= [hau [huv [hvb hs]]].
case: ifP=> hP.
- split=> //; split=> //; split=> //; exact: ih hs.
- apply: ordered_real_interval_family_lower_bound (le_trans hau (ltW huv)) _.
  exact: ih hs.
Qed.

(** Source for [ordered_real_interval_family_reset_bounds]: supporting
    interval restriction for the open-set argument in Federer 2.9.20, p. 166
    If every remaining cell has its endpoints in [a,b], its pre-existing
    order makes it eligible in that interval. *)
Lemma ordered_real_interval_family_reset_bounds (R : realType)
    (l r a b : R) (s : seq (R * R)) :
  is_ordered_real_interval_family l r s ->
  (forall u v, (u,v) \in s -> a<=u /\ v<=b) ->
  is_ordered_real_interval_family a b s.
Proof.
elim: s l a=> [//|[u v] s ih] l a /= hs hb.
have [hlu [huv [hvr hs']]] := hs.
have huvMem : (u,v) \in (u,v)::s by rewrite inE eqxx.
have [hau hvb] := hb u v huvMem.
split=> //; split=> //; split=> //.
apply: (@ih v v hs')=> p q hpq.
have [hvp [_ _]] := ordered_real_interval_family_cell_bounds hs' hpq.
split=> //; apply: (hb p q _).2; by rewrite inE hpq orbT.
Qed.
