(** Federer (1969), 2.4.12, pp. 86–87: essential
    norm and its comparison with the measure gauge. Source
    editions and the zero-measure threshold clarification:
    MeasureEssentialNormUP.v. No witness implementation is imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostBasic MeasureGauge
  MeasureEssentialNormUP MeasureEssentialNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_essential_norm]: public phi_(infinity)
    of Federer 2.4.12, p. 86, characterised by
    the sealed infimum laws. *)
Definition measure_essential_norm (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :=
  MeasureEssentialNorm.value mu N f.

(** Source for [measure_essential_norm_specification]: the
    defining infimum laws in Federer 2.4.12, p. 86. *)
Lemma measure_essential_norm_specification (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  is_measure_essential_norm mu N f (measure_essential_norm mu N f).
Proof. exact: MeasureEssentialNorm.laws. Qed.

(** Source for [measure_essential_norm_nonnegative]: nonnegativity
    required by the seminorm assertion of Federer 2.4.12,
    p. 86. Our explicit threshold convention includes null measures. *)
Lemma measure_essential_norm_nonnegative (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  0 <= measure_essential_norm mu N f.
Proof. apply: (measure_essential_norm_specification mu N f).2=> r [hr _]; exact hr. Qed.

(** Source for [measure_essential_norm_bound]: supporting
    upper bound on the infimum in Federer 2.4.12, p. 86. *)
Lemma measure_essential_norm_bound (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) r :
  measure_essential_norm_feasible mu N f r -> measure_essential_norm mu N f <= r.
Proof. exact: (measure_essential_norm_specification mu N f).1. Qed.

(** Source for [measure_essential_norm_feasible_upward]: supporting
    monotonicity of null superlevel thresholds for Federer 2.4.12, p. 86 *)
Lemma measure_essential_norm_feasible_upward (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) r s :
  measure_essential_norm_feasible mu N f r -> r <= s -> measure_essential_norm_feasible mu N f s.
Proof.
move=> [hr hb] hrs; split; first exact: le_trans hr hrs.
exact (@measure_null_subset R X mu hm _ _ (partial_norm_superlevel_antitone hrs) hb).
Qed.

(** Source for [measure_essential_norm_strict_upper_feasible]: the
    approximating thresholds used for the essential bound of Federer 2.4.12,
    p. 86 *)
Lemma measure_essential_norm_strict_upper_feasible (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f : partial_function X Y) r :
  measure_essential_norm mu N f < r -> measure_essential_norm_feasible mu N f r.
Proof.
move=> hr; have [he|he] := pselect
  (exists s, measure_essential_norm_feasible mu N f s /\ s < r).
- have [s [hs hsr]] := he; exact (@measure_essential_norm_feasible_upward R X Y mu hm N f s r hs (ltW hsr)).
- exfalso; have hb : r <= measure_essential_norm mu N f.
    apply: (measure_essential_norm_specification mu N f).2=> s hs.
    rewrite leNgt; apply/negP=> hsr; apply: he; by exists s.
  by move: hr; rewrite ltNge hb.
Qed.

(** Source for [measure_gauge_le_essential_norm]: direct bound |f|_phi <=
    phi_(infinity)(f) in Federer 2.4.12, p. 87 It already follows from the
    infimum laws without measurability. *)
Lemma measure_gauge_le_essential_norm (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (N : Y -> R) (f : partial_function X Y) :
  measure_gauge mu N f <= measure_essential_norm mu N f.
Proof.
apply: (measure_essential_norm_specification mu N f).2=> r [hr hz].
apply: measure_gauge_bound; split=> //; by rewrite hz.
Qed.
