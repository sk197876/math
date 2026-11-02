(** Federer (1969), 1.10.5, p. 48, the sums of products of factor lengths in
    the mass infimum. Real-valued input seminorms suffice for these cost
    identities. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP SymmetricDecompositions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Costs.
Variable R : realFieldType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.

(** Source for [symmetric_tuple_cost]: Federer 1.10.5,
    p. 48, the product of the m factor lengths for one summand.
    In degree zero this is the empty product one. *)
Definition symmetric_tuple_cost m (t : m.-tuple V) : R :=
  \prod_(i < m) N (tnth t i).

(** Source for [symmetric_decomposition_cost]: Federer 1.10.5,
    p. 48, the total cost of a finite list of products.
    The empty list has cost zero. *)
Definition symmetric_decomposition_cost m (s : seq (m.-tuple V)) : R :=
  \sum_(t <- s) symmetric_tuple_cost t.

(** Source for [symmetric_tuple_cost_nonnegative]: Federer 1.10.5,
    p. 48, supporting nonnegativity of each candidate product of lengths. *)
Lemma symmetric_tuple_cost_nonnegative m (t : m.-tuple V) :
  0 <= symmetric_tuple_cost t.
Proof. apply: prodr_ge0=> i _; exact: real_seminorm_nonnegative hN (tnth t i). Qed.

(** Source for [symmetric_decomposition_cost_nonnegative]: Federer
    1.10.5, p. 48, the defining infimum has lower bound zero. *)
Lemma symmetric_decomposition_cost_nonnegative m (s : seq (m.-tuple V)) :
  0 <= symmetric_decomposition_cost s.
Proof. apply: sumr_ge0=> t _; exact: symmetric_tuple_cost_nonnegative. Qed.

(** Source for [symmetric_tuple_cost_scale_first]: Federer 1.10.5,
    p. 48, supporting absolute homogeneity: absorbing a scalar in
    the first factor multiplies the cost by its absolute value. *)
Lemma symmetric_tuple_cost_scale_first m c (t : m.+1.-tuple V) :
  symmetric_tuple_cost (symmetric_scale_first_tuple c t) = `|c| * symmetric_tuple_cost t.
Proof.
rewrite /symmetric_tuple_cost
  -(@big_tuple R 1 *%R V m.+1 (symmetric_scale_first_tuple c t) predT N)
  -(@big_tuple R 1 *%R V m.+1 t predT N).
rewrite /symmetric_scale_first_tuple /= big_cons (real_seminorm_scale hN).
by rewrite [t in RHS](tuple_eta t) /= big_cons mulrA.
Qed.

(** Source for [symmetric_decomposition_cost_scale_first]: Federer
    1.10.5, p. 48, scaling every summand of a positive-degree
    decomposition multiplies the total cost by the scalar's absolute value. *)
Lemma symmetric_decomposition_cost_scale_first m c (s : seq (m.+1.-tuple V)) :
  symmetric_decomposition_cost [seq symmetric_scale_first_tuple c t | t <- s] =
    `|c| * symmetric_decomposition_cost s.
Proof.
rewrite /symmetric_decomposition_cost big_map mulr_sumr.
apply: eq_bigr=> t _; exact: symmetric_tuple_cost_scale_first.
Qed.

(** Source for [symmetric_decomposition_cost_cat]: Federer 1.10.5,
    p. 48, concatenating two decompositions adds their costs,
    the supporting step for the triangle inequality of the infimum. *)
Lemma symmetric_decomposition_cost_cat m (s t : seq (m.-tuple V)) :
  symmetric_decomposition_cost (s++t) =
    symmetric_decomposition_cost s + symmetric_decomposition_cost t.
Proof. exact: big_cat. Qed.
End Costs.
