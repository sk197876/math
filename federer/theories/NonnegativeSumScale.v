(** Federer (1969), 2.1.1(6), p. 52: real scalar factors in numerical sums,
    here the nonnegative case. Source context and conventions:
    NonnegativeSumUP.v. The zero case explicitly uses the special product
    convention of 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_finite_scale]: Federer 2.1.1(6),
    p. 52; supporting distributivity on a finite set of nonnegative
    terms, with the special zero-times-infinity convention. *)
Lemma nonnegative_finite_scale (R : realType) (I : choiceType)
    (B : {fset I}) (f : I -> \bar R) c :
  (forall x, x \in B -> 0 <= f x) ->
  c * (\sum_(x <- B) f x) = \sum_(x <- B) (c * f x).
Proof.
move=> hf; rewrite !big_seq; apply: ge0_sume_distrr; exact hf.
Qed.

(** Source for [nonnegative_sum_scale]: Federer 2.1.1(6),
    p. 52; a nonnegative finite scalar factors out of summation.
    Zero is included under the explicitly special product convention. *)
Theorem nonnegative_sum_scale (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (c : R) :
  (0 <= c)%R -> (forall x, A x -> 0 <= f x) ->
  nonnegative_sum A (fun x => c%:E * f x) = c%:E * nonnegative_sum A f.
Proof.
move=> hc hf; have [->|hc0] := eqVneq c 0%R.
- rewrite mul0e; apply: nonnegative_sum_zero=> x _; exact: mul0e.
have hcpos : (0 < c)%R by rewrite lt_def hc0 hc.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: nonnegative_sum_least=> B hB.
  rewrite -nonnegative_finite_scale; last by move=> x hx; exact: hf (hB x hx).
  apply: lee_wpmul2l; first by rewrite lee_fin.
  exact: nonnegative_sum_upper hB.
- rewrite -lee_pdivlMl //; apply: nonnegative_sum_least=> B hB.
  rewrite lee_pdivlMl // nonnegative_finite_scale; last by move=> x hx; exact: hf (hB x hx).
  exact: nonnegative_sum_upper hB.
Qed.
