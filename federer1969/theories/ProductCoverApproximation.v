(** Federer (1969), 2.6.2, proof p. 116: choose rectangle covers with costs
    approaching the product-measure infimum. This supporting consequence
    uses only the abstract sequential infimum from 2.6.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSum ProductMeasure ProductMeasureSequenceInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_sequence_strict_approximation]: supporting
    cover choice for Federer 2.6.2, p. 116 Every strict upper bound on the
    infimum admits a sequential measurable- rectangle cover with cost below
    that bound. *)
Lemma product_measure_sequence_strict_approximation (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) b :
  product_measure ha hb S < b -> exists (A : nat -> set X) (B : nat -> set Y),
    (forall n, measure_measurable alpha (A n) /\ measure_measurable beta (B n)) /\
    S `<=` (\bigcup_n (A n `*` B n)) /\
    nonnegative_sum setT (fun n => alpha (A n) * beta (B n)) < b.
Proof.
move=> hlt; apply: contrapT=> hn.
have hle : b <= product_measure ha hb S.
  apply: (product_measure_sequence_cover_greatest ha hb)=> A B hm hc.
  rewrite leNgt; apply/negP=> hs; apply: hn; exists A, B; by split=> //; split.
by have := lt_le_trans hlt hle; rewrite ltxx.
Qed.
