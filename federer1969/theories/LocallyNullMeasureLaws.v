(** Federer (1969), 2.5.14, p. 108: supporting countable exceptional-set
    arguments for local uniqueness. These are consequences of 2.1.2–2.1.3,
    pp. 53–55, applied to finite-measure tests, not extra measure axioms.
    Source context and local-convention explanation: LocallyNullMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic LocallyNullMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_locally_null_subset]: local downward
    closure of exceptional sets, supporting Federer 2.5.14,
    p. 108, from monotonicity in 2.1.2, p. 53. *)
Lemma measure_locally_null_subset (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  A `<=` B -> measure_locally_null mu B -> measure_locally_null mu A.
Proof.
move=> hAB hB T hT; apply: (@measure_null_subset R X mu hm _ (T `&` B)); last exact: hB T hT.
by move=> x [hx ha]; split=> //; exact: hAB.
Qed.

(** Source for [measure_null_is_locally_null]: global nullity
    implies its local version in Federer 2.5.14, p. 108,
    by 2.1.2, p. 53. The converse is not asserted. *)
Lemma measure_null_is_locally_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  mu A=0 -> measure_locally_null mu A.
Proof.
by move=> hA T _; apply: (@measure_null_subset R X mu hm _ A).
Qed.

(** Source for [measure_locally_null_countable_union]: countable
    unions of locally null sets are locally null, supporting
    the countable rational-density argument in Federer 2.5.14,
    p. 108, as in 2.5.12, p. 104. *)
Lemma measure_locally_null_countable_union (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (N : J -> set X) :
  countable D -> (forall j, D j -> measure_locally_null mu (N j)) ->
  measure_locally_null mu (\bigcup_(j in D) N j).
Proof.
move=> hD hN T hT.
have he : T `&` (\bigcup_(j in D) N j)=\bigcup_(j in D) (T `&` N j).
  apply/seteqP; split=> x.
  - move=> [hx [j hj hn]]; exists j=> //; by split.
  - move=> [j hj [hx hn]]; split=> //; by exists j.
rewrite he; apply: (@measure_null_countable_union R X J mu hm D _ hD)=> j hj.
exact: hN j hj T hT.
Qed.

(** Source for [measure_locally_null_measurable]: locally null
    sets satisfy Caratheodory measurability by finite tests,
    supporting the modified-density argument in Federer 2.5.14,
    p. 108. Measurability is not global nullity. *)
Lemma measure_locally_null_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : set X) :
  measure_locally_null mu N -> measure_measurable mu N.
Proof.
move=> hN; apply/(measure_measurable_finite_test hm)=> T hT.
rewrite (hN T hT) add0e; apply: (@measure_mono R X mu hm)=> x [hx _]; exact hx.
Qed.
