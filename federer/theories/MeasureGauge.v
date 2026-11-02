(** Federer (1969), 2.3.8, p. 78: the gauge defined by the measure of strict
    norm superlevel sets. The definition uses the project's abstract
    extended infimum. These order lemmas need no norm or measurability
    hypotheses. Partial domains follow Federer, including the erratum p. 1,
    book p. 78 line 7: the collection is a set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_superlevel]: Federer 2.3.8, p. 78,
    the set where the norm of a defined function value exceeds r;
    undefined points are absent, as in the book's inverse images. *)
Definition partial_norm_superlevel (R : realType) (X Y : Type)
    (N : Y -> R) (f : partial_function X Y) (r : \bar R) :=
  partial_function_preimage f [set y | r < (N y)%:E].

(** Source for [measure_gauge_feasible]: Federer 2.3.8, p. 78,
    the upper-level measure bound defining admissible thresholds.
    The redundant nonnegative condition excludes negative thresholds
    explicitly; positive infinity is admitted. *)
Definition measure_gauge_feasible (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y)
    (r : \bar R) := 0 <= r /\ mu (partial_norm_superlevel N f r) <= r.

(** Source for [measure_gauge]: Federer 2.3.8, p. 78, first
    defining display; the infimum of feasible thresholds. The value
    may be positive infinity, as expressly allowed in the text. *)
Definition measure_gauge (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :=
  extended_real_inf (measure_gauge_feasible mu N f).

(** Source for [partial_norm_superlevel_antitone]: supporting
    inclusion for the infimum argument in Federer 2.3.8, p. 78. *)
Lemma partial_norm_superlevel_antitone (R : realType) (X Y : Type)
    (N : Y -> R) (f : partial_function X Y) r s :
  r <= s -> partial_norm_superlevel N f s `<=` partial_norm_superlevel N f r.
Proof. move=> hrs x [y [hy hsy]]; exists y; split=> //; exact: le_lt_trans hrs hsy. Qed.

(** Source for [measure_gauge_feasible_upward]: supporting order
    property of the thresholds in Federer 2.3.8, p. 78. *)
Lemma measure_gauge_feasible_upward (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) r s :
  measure_gauge_feasible mu N f r -> r <= s -> measure_gauge_feasible mu N f s.
Proof.
move=> [hr hb] hrs; split; first exact: le_trans hr hrs.
have hi := @partial_norm_superlevel_antitone R X Y N f r s hrs.
apply: le_trans (@measure_mono R X mu hm _ _ hi) _.
exact: le_trans hb hrs.
Qed.

(** Source for [measure_gauge_nonnegative]: Federer 2.3.8,
    p. 78, nonnegativity of the gauge, implicit in its role as
    the distance from zero. *)
Lemma measure_gauge_nonnegative (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  0 <= measure_gauge mu N f.
Proof. apply: extended_real_inf_greatest=> r [hr _]; exact hr. Qed.

(** Source for [measure_gauge_bound]: Federer 2.3.8, p. 78,
    a feasible threshold bounds the infimum from above. *)
Lemma measure_gauge_bound (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) r :
  measure_gauge_feasible mu N f r -> measure_gauge mu N f <= r.
Proof. exact: extended_real_inf_lower. Qed.

(** Source for [measure_gauge_strict_upper_feasible]: supporting
    infimum step for the attainment assertion in Federer 2.3.8,
    p. 78; every threshold strictly above the gauge is feasible. *)
Lemma measure_gauge_strict_upper_feasible (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) r :
  measure_gauge mu N f < r -> measure_gauge_feasible mu N f r.
Proof.
move=> hr; have [he|he] := pselect
  (exists s, measure_gauge_feasible mu N f s /\ s < r).
- have [s [hs hsr]] := he; exact (@measure_gauge_feasible_upward R X Y mu hm N f s r hs (ltW hsr)).
- exfalso; have hb : r <= measure_gauge mu N f.
    apply: extended_real_inf_greatest=> s hs.
    rewrite leNgt; apply/negP=> hsr; apply: he; by exists s.
  by move: hr; rewrite ltNge hb.
Qed.
