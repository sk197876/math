(** Private recursive choice for Federer (1969), 2.3.10, p. 80. At each step
    take the maximum of the next Cauchy cutoff and one more than the
    preceding index. Source context: CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order boolp classical_sets reals constructive_ereal.
From Federer Require Import CauchyIndexSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [increasing_cutoff_recursion]: private construction
    of strictly increasing cutoffs for Federer 2.3.10, p. 80. *)
Fixpoint increasing_cutoff_recursion (K : nat -> nat) n :=
  if n is m.+1 then maxn (K n) (increasing_cutoff_recursion K m).+1 else K 0%N.

(** Source for [increasing_cutoff_recursion_upper]: the recursive
    cutoffs dominate the originally chosen Cauchy cutoffs, supporting
    Federer 2.3.10, p. 80. *)
Lemma increasing_cutoff_recursion_upper (K : nat -> nat) n :
  (K n <= increasing_cutoff_recursion K n)%N.
Proof. case: n=> [|n]; first exact: leqnn. exact: leq_maxl. Qed.

(** Source for [cauchy_index_selection_exists]: existence of the
    increasing choices in Federer 2.3.10, p. 80, derived
    from the supplied Cauchy cutoffs without project axioms. *)
Theorem cauchy_index_selection_exists (R : realType) (d : nat -> nat -> \bar R)
    (b : nat -> R) :
  (forall n, exists K, forall i j, (K <= i)%N -> (K <= j)%N -> d i j < (b n)%:E) ->
  exists s, is_cauchy_index_selection d b s.
Proof.
move=> hc; pose K n := projT1 (cid (hc n)).
have hK n := projT2 (cid (hc n)).
exists (increasing_cutoff_recursion K); split.
- move=> n; exact: leq_maxr.
- move=> n i j hi hj; apply: hK.
  + exact: leq_trans (increasing_cutoff_recursion_upper K n) hi.
  + exact: leq_trans (increasing_cutoff_recursion_upper K n) hj.
Qed.
