(** Federer (1969), 2.4.9, p. 85: the pointwise differences |fn-g| and
    2h-|fn-g| used in the Fatou proof. Here 2h is h+h; this has exactly the
    same graph, including infinite values. All calculations in the
    supporting lemmas below take place on the conull finite-value region.
    Source context: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic
  PartialAbsolutePartsGraph PartialDominatedConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [partial_finite_sum_graph]: supporting finite
    addition for the expression 2h in Federer 2.4.9, p. 85. *)
Lemma partial_finite_sum_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x (a b : R) :
  partial_function_graph f x a%:E -> partial_function_graph g x b%:E ->
  partial_function_graph (partial_extended_function_add f g) x (a+b)%:E.
Proof.
move=> hf hg; apply/partial_extended_function_add_graph.
exists a%:E,b%:E; split=> //; split=> //; by rewrite /extended_add /=.
Qed.

(** Source for [partial_finite_difference_graph]: supporting
    finite subtraction in Federer 2.4.9, p. 85. *)
Lemma partial_finite_difference_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x (a b : R) :
  partial_function_graph f x a%:E -> partial_function_graph g x b%:E ->
  partial_function_graph (partial_extended_function_subtract f g) x (a-b)%:E.
Proof.
move=> hf hg; apply/partial_extended_function_add_graph.
exists a%:E,(-b)%:E; split=> //; split.
- exists b%:E; by split.
- by rewrite /extended_add /=.
Qed.

(** Source for [partial_absolute_difference]: the function
    |fn-g| occurring in Federer 2.4.9, p. 85;
    undefined subtraction of equal infinities remains excluded. *)
Definition partial_absolute_difference (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :=
  partial_extended_function_absolute_value (partial_extended_function_subtract f g).

(** Source for [partial_dominated_complement]: the nonnegative
    test sequence 2h-|fn-g| in Federer 2.4.9,
    p. 85, written with 2h=h+h. *)
Definition partial_dominated_complement (R : realType) (X : Type)
    (f g h : partial_function X (extended_real_line R)) :=
  partial_extended_function_subtract (partial_extended_function_add h h) (partial_absolute_difference f g).

(** Source for [partial_finite_absolute_difference_graph]:
    supporting evaluation of the error in Federer 2.4.9, p. 85. *)
Lemma partial_finite_absolute_difference_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x (a b : R) :
  partial_function_graph f x a%:E -> partial_function_graph g x b%:E ->
  partial_function_graph (partial_absolute_difference f g) x `|a-b|%:E.
Proof.
move=> hf hg; exists (a-b)%:E; split; last by [].
exact: partial_finite_difference_graph hf hg.
Qed.

(** Source for [partial_finite_complement_graph]: supporting
    evaluation of 2h-|fn-g| on the finite-value region
    in Federer 2.4.9, p. 85. *)
Lemma partial_finite_complement_graph (R : realType) (X : Type)
    (f g h : partial_function X (extended_real_line R)) x (a b c : R) :
  partial_function_graph f x a%:E -> partial_function_graph g x b%:E ->
  partial_function_graph h x c%:E ->
  partial_function_graph (partial_dominated_complement f g h) x (c+c-`|a-b|)%:E.
Proof.
move=> hf hg hh; apply: partial_finite_difference_graph.
- exact (@partial_finite_sum_graph R X h h x c c hh hh).
- exact: partial_finite_absolute_difference_graph hf hg.
Qed.

(** Source for [dominated_real_complement_nonnegative]: the
    pointwise nonnegativity of 2h-|fn-g| in Federer
    2.4.9, p. 85, from the triangle inequality. *)
Lemma dominated_real_complement_nonnegative (R : realType) (a b c : R) :
  (`|a| <= c)%R -> (`|b| <= c)%R -> (0 <= c+c-`|a-b|)%R.
Proof.
move=> ha hb; rewrite subr_ge0; apply: le_trans (ler_normB a b) _.
exact: lerD ha hb.
Qed.
