(** Federer (1969), 1.7.5, p. 33: grouping coordinate products by output
    index in the general wedge estimate. These scalar lemmas isolate
    Cauchy's inequality and the fact that each pair contributes to at most
    one output coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import FiniteSumCauchy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unique_support_sum_bound]: Federer 1.7.5,
    p. 33, supporting summation fact: a nonnegative term counted
    at most once contributes at most its own value. *)
Lemma unique_support_sum_bound (R : realFieldType) (I : finType)
    (P : pred I) (a : R) : 0 <= a ->
    (forall i j, P i -> P j -> i = j) -> (\sum_(i | P i) a) <= a.
Proof.
move=> ha hu; case: (boolP [exists i, P i]) => [/existsP[i hi]|hn].
- rewrite (bigD1 i hi) /=.
  have hz : (\sum_(j | P j && (j != i)) a) = 0.
    apply: big1 => j /andP[hj hji]; have he := hu j i hj hi.
    by rewrite he eqxx in hji.
  by rewrite hz addr0 lexx.
- have hz : (\sum_(i | P i) a) = 0.
    apply: big1 => i hi; have he : [exists j, P j] by apply/existsP; exists i.
    by rewrite he in hn.
  by rewrite hz.
Qed.

(** Source for [finite_sparse_sum_squared_bound]: Federer
    1.7.5, p. 33, supporting form of the final estimate:
    if each output has at most M contributing terms and each
    term appears in at most one output, the sum of squared output
    sums is bounded by M times the sum of squared input terms. *)
Theorem finite_sparse_sum_squared_bound (R : realFieldType)
    (I J : finType) (S : I -> J -> bool) (a : I -> R) M :
  (forall j, (#|[pred i | S i j]| <= M)%N) ->
  (forall i j k, S i j -> S i k -> j = k) ->
  (\sum_j (\sum_(i | S i j) a i)^+2) <= M%:R * \sum_i (a i)^+2.
Proof.
move=> hc hu.
apply: le_trans (_ : M%:R * (\sum_j \sum_(i | S i j) (a i)^+2) <= _).
- rewrite mulr_sumr; apply: ler_sum => j _.
  apply: le_trans (@finite_sum_cauchy_squared R I (fun i => S i j) a) _.
  apply: ler_wpM2r.
  + apply: sumr_ge0 => i _; exact: sqr_ge0.
  + by rewrite ler_nat; exact: hc.
- apply: ler_wpM2l; first exact: ler0n.
  rewrite (exchange_big_dep predT) //=.
  apply: ler_sum => i _; apply: unique_support_sum_bound; first exact: sqr_ge0.
  exact: hu.
Qed.
