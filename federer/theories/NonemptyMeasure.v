(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonempty_measure]: Federer 2.1.2, p. 54, example assigning
    zero to the empty set and one to every nonempty set. This explicit
    function witnesses the possibility that only the empty and whole sets
    are measurable. *)
Definition nonempty_measure (R : realType) (I : choiceType) (A : set I) : \bar R :=
  if A == set0 then 0 else (1 : R)%:E.
Arguments nonempty_measure {R I} A.

(** Source for [nonempty_measure_ge0]: Federer 2.1.2,
    p. 54; supporting nonnegativity of the example's two values. *)
Lemma nonempty_measure_ge0 (R : realType) (I : choiceType) (A : set I) :
  0 <= nonempty_measure (R := R) A.
Proof. by rewrite /nonempty_measure; case: ifP=> _; rewrite ?lee_fin ?ler01. Qed.

(** Source for [nonempty_measure_is_measure]: Federer 2.1.2,
    p. 54; verification that the zero-or-one example is a measure.
    A covering of a nonempty set has a nonempty member. *)
Lemma nonempty_measure_is_measure (R : realType) (I : choiceType) :
  is_measure (@nonempty_measure R I).
Proof.
constructor; first exact: nonempty_measure_ge0.
move=> A F _ hc; rewrite /nonempty_measure; case: ifP=> hA.
- exact: nonnegative_sum_nonnegative.
- have hA0 : A != set0 by rewrite hA.
  have [x hx] := proj1 (set0P A) hA0.
  have [B hB hxB] := hc x hx.
  have hB0 : B != set0 by apply/eqP=> he; rewrite he in hxB.
  have ht := @nonnegative_sum_term R _ F (@nonempty_measure R I) B hB.
  by rewrite /nonempty_measure (negbTE hB0) in ht.
Qed.

(** Source for [nonempty_measure_measurable_iff]: Federer 2.1.2, p. 54;
    exactly the empty and whole sets are measurable for this example. The
    statement includes empty and singleton ambient spaces. *)
Lemma nonempty_measure_measurable_iff (R : realType) (I : choiceType)
    (A : set I) :
  measure_measurable (@nonempty_measure R I) A <-> A = set0 \/ A = setT.
Proof.
split.
- move=> h; have [h0|h0] := eqVneq A set0; first by left.
  have [hT|hT] := eqVneq A setT; first by right.
  exfalso.
  have hC : ~` A != set0.
    apply/negP=> /eqP he.
    have hAT : A = setT by rewrite -(setCK A) he setC0.
    by move: hT; rewrite hAT eqxx.
  have [x hx] := proj1 (set0P A) h0.
  have hX : (@setT I) != set0 by apply/eqP=> he; have ht : (@setT I) x by []; rewrite he in ht.
  have he := h setT.
  rewrite setTI setTD /nonempty_measure (negbTE hX) (negbTE h0) (negbTE hC) in he.
  have hlt : (1 : \bar R) < 1 + 1 by rewrite -EFinD lte_fin ltrDl ltr01.
  by rewrite -he ltxx in hlt.
- case=> ->; [exact: (@measure_measurable_empty R I _ (@nonempty_measure_is_measure R I)) |
    exact: (@measure_measurable_whole R I _ (@nonempty_measure_is_measure R I))].
Qed.
