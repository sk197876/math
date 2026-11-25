(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_restrict]: Federer 2.1.2, p. 54, definition of
    restriction, (phi L Y)(A) = phi(Y intersection A). The domain remains
    all subsets of X, and Y need not be measurable. *)
Definition measure_restrict (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (Y : set I) (A : set I) := mu (Y `&` A).

(** Source for [measure_restrict_is_measure]: Federer 2.1.2, p. 54,
    restriction is another measure over X. *)
Lemma measure_restrict_is_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (Y : set I) :
  is_measure (measure_restrict mu Y).
Proof.
constructor; first by move=> A; exact: (@measure_nonnegative R I mu hm).
move=> A F hF hc; apply: (@measure_indexed_cover R I _ mu hm _ F _ hF).
move=> x [hY hA]; have [B hB hxB] := hc x hA.
by exists B; last split.
Qed.

(** Source for [measure_restrict_measurable]: Federer 2.1.2, p. 54, every
    phi measurable set is phi L Y measurable. No measurability condition on
    Y. *)
Lemma measure_restrict_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (Y A : set I) :
  measure_measurable mu A -> measure_measurable (measure_restrict mu Y) A.
Proof.
move=> h T; rewrite /measure_restrict (h (Y `&` T)).
by rewrite setIA setIDA.
Qed.
