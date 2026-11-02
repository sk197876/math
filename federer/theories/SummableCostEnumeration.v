(** Federer (1969), 2.10.22, pp. 184–185: public positive-cost cover
    enumeration through its sealed selection laws. The private greedy state
    is not exported. Source context and proof route:
    SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum SummableCostEnumerationUP SummableCostEnumerationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [summable_cost_enumeration]: supporting
    cost-ordered optional cover sequence in 2.10.22,
    pp. 184–185, using only the sealed witness. *)
Definition summable_cost_enumeration (R : realType) (I : choiceType) (G : set I) (w : I -> R) (M : R)
    (hw : forall x, G x -> 0<=w x) (hs : (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E) :=
  @SummableCostEnumeration.value R I G w M hw hs.

(** Source for [summable_cost_enumeration_specification]: abstract
    membership, injectivity, positive coverage and
    late-cost control for 2.10.22, pp. 184–185. *)
Lemma summable_cost_enumeration_specification (R : realType) (I : choiceType) (G : set I) (w : I -> R) (M : R)
    (hw : forall x, G x -> 0<=w x) (hs : (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E) :
  is_summable_cost_enumeration G w M (@summable_cost_enumeration R I G w M hw hs).
Proof. exact: SummableCostEnumeration.laws. Qed.
