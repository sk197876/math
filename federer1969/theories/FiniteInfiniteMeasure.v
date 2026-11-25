(** Federer (1969), 2.1.5, p. 57, first irregular-measure example: zero on
    the empty set, one on nonempty finite sets, and two on infinite sets.
    The ambient space is explicitly infinite in the classification below, as
    Federer requires. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit BoundedNonemptyMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_infinite_measure]: Federer 2.1.5, p. 57, first
    counterexample. The printed value one for finite sets is understood for
    nonempty finite sets, consistently with the preceding explicit value
    zero at the empty set. *)
Definition finite_infinite_measure (R : realType) (I : choiceType) (A : set I) : \bar R :=
  if A == set0 then 0 else if pselect (finite_set A) then (1 : R)%:E else (2 : R)%:E.
Arguments finite_infinite_measure {R I} A.

(** Source for [finite_infinite_measure_empty]: Federer
    2.1.5, p. 57, first counterexample's empty-set value. *)
Lemma finite_infinite_measure_empty (R : realType) (I : choiceType) :
  @finite_infinite_measure R I set0 = 0.
Proof. by rewrite /finite_infinite_measure eqxx. Qed.

(** Source for [finite_infinite_measure_finite]: Federer
    2.1.5, p. 57, first counterexample's value on nonempty finite sets. *)
Lemma finite_infinite_measure_finite (R : realType) (I : choiceType) (A : set I) :
  A != set0 -> finite_set A -> finite_infinite_measure (R := R) A = (1 : R)%:E.
Proof.
move=> ha hf; rewrite /finite_infinite_measure (negbTE ha).
by case: (pselect (finite_set A))=> // hn; exfalso; exact: hn.
Qed.

(** Source for [finite_infinite_measure_infinite]: Federer
    2.1.5, p. 57, first counterexample's value on infinite sets. *)
Lemma finite_infinite_measure_infinite (R : realType) (I : choiceType) (A : set I) :
  infinite_set A -> finite_infinite_measure (R := R) A = (2 : R)%:E.
Proof.
move=> hi; have ha : A != set0 by apply/eqP=> he; apply: hi; rewrite he; exact: finite_set0.
rewrite /finite_infinite_measure (negbTE ha).
by case: (pselect (finite_set A))=> // hf; exfalso; exact: hi.
Qed.

(** Source for [finite_infinite_measure_is_measure]: Federer 2.1.5, p. 57,
    verification of the first counterexample's measure law. the
    bounded-nonempty covering principle proves it here. *)
Lemma finite_infinite_measure_is_measure (R : realType) (I : choiceType) :
  is_measure (@finite_infinite_measure R I).
Proof.
apply: bounded_nonempty_is_measure.
- exact: finite_infinite_measure_empty.
- move=> A B hAB; have [ha|ha] := eqVneq A set0.
  + rewrite ha finite_infinite_measure_empty /finite_infinite_measure.
    case: ifP=> _; first exact: lexx.
    by case: (pselect (finite_set B))=> hfinB; rewrite lee_fin ?ler01 ?ler0n.
  + have hb : B != set0.
      apply/eqP=> he; have [x hx] := proj1 (set0P A) ha.
      have h := hAB x hx; by rewrite he in h.
    rewrite /finite_infinite_measure (negbTE ha) (negbTE hb).
    case: (pselect (finite_set A))=> hA; case: (pselect (finite_set B))=> hB;
      try by rewrite lee_fin ?lexx ?ler1n.
    exfalso; apply: hA; exact: sub_finite_set hAB hB.
- move=> A ha; rewrite /finite_infinite_measure (negbTE ha).
  by case: (pselect (finite_set A))=> hfinA; rewrite lee_fin ?lexx ?ler1n.
- move=> A; rewrite /finite_infinite_measure; case: ifP=> _.
  + by rewrite lee_fin ?ler01 ?ler0n.
  + by case: (pselect (finite_set A))=> hfinA; rewrite lee_fin ?lexx ?ler1n.
Qed.

(** Source for [finite_infinite_measure_nonempty_lower]: Federer
    2.1.5, p. 57, supporting bound used to identify measurable sets
    in the first counterexample. Every nonempty set has value at least one. *)
Lemma finite_infinite_measure_nonempty_lower (R : realType) (I : choiceType) (A : set I) :
  A != set0 -> (1 : R)%:E <= finite_infinite_measure (R := R) A.
Proof.
move=> ha; rewrite /finite_infinite_measure (negbTE ha).
by case: (pselect (finite_set A))=> hfinA; rewrite lee_fin ?lexx ?ler1n.
Qed.

(** Source for [finite_infinite_measure_measurable_iff]: Federer 2.1.5, p.
    57, supporting classification for failures of (1),(2). *)
Theorem finite_infinite_measure_measurable_iff (R : realType) (I : choiceType)
    (A : set I) : infinite_set (@setT I) ->
  (measure_measurable (@finite_infinite_measure R I) A <-> A = set0 \/ A = setT).
Proof.
move=> hX; split.
- move=> hm; have [h0|h0] := eqVneq A set0; first by left.
  have [hT|hT] := eqVneq A setT; first by right.
  exfalso; have hC : ~` A != set0.
    apply/negP=> /eqP he; have hAT : A = setT by rewrite -(setCK A) he setC0.
    by move: hT; rewrite hAT eqxx.
  have he := hm setT.
  rewrite setTI setTD (@finite_infinite_measure_infinite R I setT hX) in he.
  have hl : (2 : R)%:E < finite_infinite_measure (R := R) A + finite_infinite_measure (R := R) (~` A).
    case: (pselect (finite_set A))=> hA.
    + have hCI : infinite_set (~` A).
        have h := infinite_setD hX hA; by rewrite setTD in h.
      rewrite (@finite_infinite_measure_finite R I A h0 hA) (@finite_infinite_measure_infinite R I (~` A) hCI).
      by rewrite -EFinD lte_fin ltrDr ltr01.
    + rewrite (@finite_infinite_measure_infinite R I A hA).
      apply: lt_le_trans (_ : (2 : R)%:E < (2 : R)%:E + (1 : R)%:E) _.
      * by rewrite -EFinD lte_fin ltrDl ltr01.
      * apply: leeD2l; exact: (@finite_infinite_measure_nonempty_lower R I (~` A) hC).
  by rewrite -he ltxx in hl.
- case=> ->.
  + exact: (@measure_measurable_empty R I _ (@finite_infinite_measure_is_measure R I)).
  + exact: (@measure_measurable_whole R I _ (@finite_infinite_measure_is_measure R I)).
Qed.
