(** Federer (1969), 1.8.1, p. 38: the convex-hull representation uses
    strictly positive coefficients. This supporting lemma deletes zero
    coefficients without increasing the number of terms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_coefficient_reduction]: Federer 1.8.1,
    p. 38, supporting deletion of terms with zero coefficient.
    The total coefficient and weighted vector are both preserved. *)
Theorem positive_coefficient_reduction (R : realFieldType) (V : lmodType R)
    (S : set V) n (u : 'I_n -> V) (a : 'I_n -> R) :
  (forall i, S (u i)) -> (forall i, 0 <= a i) ->
  exists k, exists v : 'I_k -> V, exists b : 'I_k -> R,
    (k <= n)%N /\ (forall i, S (v i)) /\ (forall i, 0 < b i) /\
    \sum_i b i = \sum_i a i /\ \sum_i b i *: v i = \sum_i a i *: u i.
Proof.
elim: n u a => [|n ih] u a hu ha.
- exists 0%N, u, a; split=> //; split=> //; split.
  + move=> i; by have := ltn_ord i; rewrite ltn0.
  + by [].
have [hz|hz] := boolP [exists i, a i == 0].
- case/existsP: hz => j /eqP hj.
  pose v (i : 'I_n) := u (lift j i).
  pose b (i : 'I_n) := a (lift j i).
  have hv i : S (v i) := hu (lift j i).
  have hb i : 0 <= b i := ha (lift j i).
  have [k [w [c [hkn [hw [hc [hs hx]]]]]]] := ih v b hv hb.
  exists k, w, c; split; first exact: leq_trans hkn (leqnSn n).
  split=> //; split=> //; split.
  + have heq : (\sum_i a i) = a j + \sum_i b i by rewrite (bigD1_ord j).
    by rewrite heq hj add0r.
  + have heq : (\sum_i a i *: u i) = a j *: u j + \sum_i b i *: v i.
      by rewrite (bigD1_ord j).
    by rewrite heq hj scale0r add0r.
- exists n.+1, u, a; split=> //; split=> //; split; last by [].
  move=> i; rewrite lt0r ha andbT.
  move/existsPn: hz => /(_ i); by rewrite eq_sym.
Qed.
