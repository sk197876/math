(** Federer (1969), 2.10.22, pp. 184–185: seal the proved positive-cost
    enumeration witness. Only membership, active injectivity, positive
    coverage and the uniform position bound are exposed. Source context and
    proof-route explanation: SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum SummableCostEnumerationUP SummableCostEnumerationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type SummableCostEnumerationSignature.
(** Source for [value]: abstract optional enumeration
    for the cover selection in 2.10.22,
    pp. 184–185, after its existence is proved. *)
Parameter value : forall (R : realType) (I : choiceType) (G : set I) (w : I -> R) (M : R),
  (forall x, G x -> 0<=w x) -> (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E -> nat -> option I.
(** Source for [laws]: the four abstract selection
    laws supporting 2.10.22, pp. 184–185. *)
Parameter laws : forall (R : realType) (I : choiceType) (G : set I) (w : I -> R) (M : R)
  (hw : forall x, G x -> 0<=w x) (hs : (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E),
  is_summable_cost_enumeration G w M (@value R I G w M hw hs).
End SummableCostEnumerationSignature.
Module SummableCostEnumeration : SummableCostEnumerationSignature.
(** Source for [value]: private selection of the
    proved enumeration witness for 2.10.22,
    pp. 184–185. *)
Definition value (R : realType) (I : choiceType) (G : set I) (w : I -> R) (M : R)
    (hw : forall x, G x -> 0<=w x) (hs : (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E) :=
  projT1 (cid (@summable_cost_enumeration_exists R I G w M hw hs)).
(** Source for [laws]: the selected witness satisfies
    the specified cover-selection laws, 2.10.22,
    pp. 184–185. *)
Lemma laws (R : realType) (I : choiceType) (G : set I) (w : I -> R) (M : R)
    (hw : forall x, G x -> 0<=w x) (hs : (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E) :
  is_summable_cost_enumeration G w M (@value R I G w M hw hs).
Proof. exact: projT2 (cid (@summable_cost_enumeration_exists R I G w M hw hs)). Qed.
End SummableCostEnumeration.
