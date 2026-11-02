(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumProduct NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_cover]: Federer 2.1.2, pp. 53-54, supporting
    covering inequality for the counting example. The proof uses the two
    iterated sums of 2.1.1(10), p. 53 (. This inequality holds for arbitrary
    covers, without a countability hypothesis. *)
Lemma nonnegative_sum_cover (R : realType) (I J : choiceType)
    (A : set I) (D : set J) (F : J -> set I) (f : I -> \bar R) :
  (forall x, 0 <= f x) -> A `<=` \bigcup_(j in D) F j ->
  nonnegative_sum A f <= nonnegative_sum D (fun j => nonnegative_sum (F j) f).
Proof.
move=> hf hc.
pose g (p : I * J) := if p.1 \in F p.2 then f p.1 else 0.
have hg : forall p, (A `*` D) p -> 0 <= g p.
  by move=> [x j] _; rewrite /g /=; case: ifP=> _; [exact: hf | exact: lexx].
have hfirst := @nonnegative_sum_product_first R I J A D g hg.
have hsecond := @nonnegative_sum_product_second R I J A D g hg.
apply: le_trans (_ : _ <= nonnegative_sum (A `*` D) g) _.
- rewrite hfirst; apply: nonnegative_sum_mono=> x hx.
  have [j hj hxj] := hc x hx.
  have ht := @nonnegative_sum_term R J D (fun j => g (x,j)) j hj.
  by rewrite /g /= (mem_set hxj) in ht.
- rewrite hsecond; apply: nonnegative_sum_mono=> j hj.
  rewrite /g nonnegative_sum_restrict.
  apply: nonnegative_sum_subset=> x [hx hxj]; exact hxj.
Qed.
