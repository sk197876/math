(** Federer (1969), 2.4.12, p. 87: the infinity-endpoint completeness
    argument through convergence in measure and an almost-everywhere
    convergent subsequence. These statements retain partial domains and
    allow infinite individual norms; membership in the finite-norm Lebesgue
    space is a separate condition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialNormedArithmetic MeasureEssentialNorm MeasureConvergenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_distance]: difference seminorm
    for the p=infinity convergence in Federer 2.4.12, p. 87. *)
Definition measure_essential_distance (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f g : partial_function X V) :=
  measure_essential_norm mu N (partial_vector_subtract f g).

(** Source for [converges_in_essential_norm]: epsilon formulation
    of convergence at p=infinity in Federer 2.4.12, p. 87. *)
Definition converges_in_essential_norm (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R)
    (f : nat -> partial_function X V) (g : partial_function X V) :=
  forall e : R, (0 < e)%R -> exists K, forall n, (K <= n)%N ->
    measure_essential_distance mu N (f n) g < e%:E.

(** Source for [cauchy_in_essential_norm]: epsilon Cauchy condition
    at p=infinity in Federer 2.4.12, p. 87. *)
Definition cauchy_in_essential_norm (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f : nat -> partial_function X V) :=
  forall e : R, (0 < e)%R -> exists K, forall n m,
    (K <= n)%N -> (K <= m)%N -> measure_essential_distance mu N (f n) (f m) < e%:E.

(** Source for [essential_norm_cauchy_in_measure]: direct endpoint
    implication in Federer 2.4.12, p. 87 *)
Lemma essential_norm_cauchy_in_measure (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R) (f : nat -> partial_function X V) :
  cauchy_in_essential_norm mu N f -> cauchy_in_measure mu N f.
Proof.
move=> hc e he; have [K hK] := hc e he; exists K=> n m hn hm.
exact: le_lt_trans (measure_gauge_le_essential_norm mu N _) (hK n m hn hm).
Qed.

(** Source for [essential_norm_converges_in_measure]: supporting
    convergence consequence of the bound in Federer 2.4.12,
    p. 87; no finite-measure source hypothesis is needed. *)
Lemma essential_norm_converges_in_measure (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (N : V -> R)
    (f : nat -> partial_function X V) (g : partial_function X V) :
  converges_in_essential_norm mu N f g -> converges_in_measure mu N f g.
Proof.
move=> hc e he; have [K hK] := hc e he; exists K=> n hn.
exact: le_lt_trans (measure_gauge_le_essential_norm mu N _) (hK n hn).
Qed.
