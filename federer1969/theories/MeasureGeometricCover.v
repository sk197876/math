(** Federer (1969), 2.2.2, p. 61: countably many chosen errors have small
    union measure. We use a half-error geometric budget and the locally
    proved covering and numerical-summation laws. Source context and the
    tolerance convention: GeometricErrorBudget.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureIndexedCover GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_geometric_cover_bound]: Federer 2.2.2,
    p. 61, supporting error-union estimate. Covering a set by
    errors bounded by the chosen geometric tolerances gives measure
    at most epsilon/2 and hence strictly less than epsilon. *)
Lemma measure_geometric_cover_bound (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A : set I)
    (E : nat -> set I) (epsilon : R) : (0 < epsilon)%R ->
  A `<=` \bigcup_n E n ->
  (forall n, mu (E n) < (geometric_error_budget epsilon n)%:E) ->
  mu A <= (epsilon / 2)%:E /\ mu A < epsilon%:E.
Proof.
move=> he hc hE.
have hb : mu A <= (epsilon / 2)%:E.
  apply: le_trans (@measure_indexed_cover R I _ mu hm A setT E (countableP _) hc) _.
  apply: le_trans _ (geometric_error_sum_bound he).
  apply: nonnegative_sum_mono=> n _; exact: ltW (hE n).
split=> //; apply: le_lt_trans hb _; rewrite lte_fin.
by rewrite ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
Qed.
