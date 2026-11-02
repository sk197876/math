(** Countable-family error allocation for the covering proof of Federer
    (1969), 2.10.1, p. 170, used in the 2.3.8 counterexample construction.
    This adapter uses a countable injection into the natural numbers and the
    already proved geometric budget. Source context:
    CountableCoverEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumProduct GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_geometric_error_budget]: supporting summable
    positive errors for a countable family, Federer 2.10.1, p. 170 The total
    is at most epsilon/2, leaving room for strict approximation even when
    the family is finite or empty. *)
Lemma countable_geometric_error_budget (R : realType) (J : choiceType)
    (D : set J) (e : R) : countable D -> (0 < e)%R ->
  exists b : J -> R, (forall j, (0 < b j)%R) /\
    nonnegative_sum D (fun j => (b j)%:E) <= (e/2)%:E.
Proof.
move=> /countable_injP[g hg] he.
exists (fun j => geometric_error_budget e (g j)); split.
- move=> j; exact: geometric_error_budget_positive.
- have hi x y : D x -> D y -> g x = g y -> x=y.
    move=> hx hy; exact: hg (mem_set hx) (mem_set hy).
  have hb j : D j -> 0 <= (geometric_error_budget e (g j))%:E.
    move=> _; exact: ltW (geometric_error_budget_positive (g j) he).
  rewrite -(@nonnegative_sum_injective_image R J nat D g
    (fun n => (geometric_error_budget e n)%:E) hi hb).
  apply: le_trans _ (geometric_error_sum_bound he).
  apply: nonnegative_sum_subset=> n hn; exact Logic.I.
Qed.
