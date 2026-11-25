(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumSealed NonnegativeSum CountingMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_measure_exists]: Federer 2.1.2,
    p. 54, existence of counting measure. A sum of unit point masses
    witnesses the abstract specification. This construction is private. *)
Lemma counting_measure_exists (R : realType) (I : choiceType) :
  exists mu : set I -> \bar R, is_counting_measure mu.
Proof.
exists (fun A => nonnegative_sum A (fun _ => (1 : R)%:E)).
move=> A; exact: NonnegativeSum.laws.
Qed.
