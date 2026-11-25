(** Federer (1969), 2.1.5, p. 57, second irregular-measure example: zero on
    the empty set, two on the whole space and one on nonempty proper
    subsets. Federer uses a three-point space; this supporting construction
    works on any ambient type. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP BoundedNonemptyMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_set_measure]: Federer 2.1.5, p. 57,
    second counterexample's set function. The empty-set branch takes
    precedence, so the supporting definition also covers empty spaces. *)
Definition full_set_measure (R : realType) (I : choiceType) (A : set I) : \bar R :=
  if A == set0 then 0 else if A == setT then (2 : R)%:E else (1 : R)%:E.
Arguments full_set_measure {R I} A.

(** Source for [full_set_measure_empty]: Federer 2.1.5,
    p. 57, second example's value zero at the empty set. *)
Lemma full_set_measure_empty (R : realType) (I : choiceType) :
  @full_set_measure R I set0 = 0.
Proof. by rewrite /full_set_measure eqxx. Qed.

(** Source for [full_set_measure_whole]: Federer 2.1.5,
    p. 57, second example's value two on the nonempty whole space. *)
Lemma full_set_measure_whole (R : realType) (I : choiceType) (x : I) :
  @full_set_measure R I setT = (2 : R)%:E.
Proof.
have hX : (@setT I) != set0 by apply/eqP=> he; have hx : (@setT I) x by []; rewrite he in hx.
by rewrite /full_set_measure (negbTE hX) eqxx.
Qed.

(** Source for [full_set_measure_proper]: Federer 2.1.5,
    p. 57, second example's value one on nonempty proper subsets. *)
Lemma full_set_measure_proper (R : realType) (I : choiceType) (A : set I) :
  A != set0 -> A != setT -> full_set_measure (R := R) A = (1 : R)%:E.
Proof. by move=> h0 hT; rewrite /full_set_measure (negbTE h0) (negbTE hT). Qed.

(** Source for [full_set_measure_is_measure]: Federer
    2.1.5, p. 57, verification of the second example's measure law.
    Monotonicity and the one-to-two bounds imply its covering inequality. *)
Lemma full_set_measure_is_measure (R : realType) (I : choiceType) :
  is_measure (@full_set_measure R I).
Proof.
apply: bounded_nonempty_is_measure.
- exact: full_set_measure_empty.
- move=> A B hAB; have [ha|ha] := eqVneq A set0.
  + rewrite ha full_set_measure_empty /full_set_measure.
    by case: ifP=> _; last case: ifP=> _; rewrite ?lee_fin ?ler01 ?ler0n.
  + have hb : B != set0.
      apply/eqP=> he; have [x hx] := proj1 (set0P A) ha.
      have h := hAB x hx; by rewrite he in h.
    rewrite /full_set_measure (negbTE ha) (negbTE hb).
    case: ifP=> [/eqP hAT|hAT]; last by case: ifP=> _; rewrite lee_fin ?lexx ?ler1n.
    have hBT : B = setT.
      apply/seteqP; split=> [x _|x _] //; apply: hAB; by rewrite hAT.
    by rewrite hBT eqxx.
- move=> A ha; rewrite /full_set_measure (negbTE ha).
  by case: ifP=> _; rewrite lee_fin ?lexx ?ler1n.
- move=> A; rewrite /full_set_measure; case: ifP=> _.
  + by rewrite lee_fin ler0n.
  + by case: ifP=> _; rewrite lee_fin ?lexx ?ler1n.
Qed.
