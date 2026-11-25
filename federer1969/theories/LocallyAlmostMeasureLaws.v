(** Federer (1969), 2.5.14, p. 108: supporting logical rules for local
    almost-everywhere statements. They are the finite-test analogues of the
    conventions in 2.3.1, p. 72, and the countable exceptional-set argument
    of 2.5.12, p. 104. Source context: LocallyNullMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic
  LocallyNullMeasureUP LocallyNullMeasureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_locally_almost_mono]: implication for
    local almost-everywhere assertions in Federer 2.5.14,
    p. 108, using 2.3.1, p. 72. *)
Lemma measure_locally_almost_mono (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (P Q : set X) :
  P `<=` Q -> measure_locally_almost_everywhere mu P -> measure_locally_almost_everywhere mu Q.
Proof.
move=> hPQ hP; apply: (@measure_locally_null_subset R X mu hm (~` Q) (~` P))=> //.
by move=> x hn hp; apply: hn; exact: hPQ.
Qed.

(** Source for [measure_locally_almost_countable]: common
    local exceptional set for the countable rational-coordinate
    argument of Federer 2.5.12, p. 104, as used in
    2.5.14, p. 108. *)
Lemma measure_locally_almost_countable (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (P : J -> set X) :
  countable D -> (forall j, D j -> measure_locally_almost_everywhere mu (P j)) ->
  measure_locally_almost_everywhere mu (\bigcap_(j in D) P j).
Proof.
move=> hc hp; rewrite /measure_locally_almost_everywhere setC_bigcap.
exact: (@measure_locally_null_countable_union R X J mu hm D (fun j => ~` P j) hc hp).
Qed.

(** Source for [measure_locally_almost_on_finite]: local
    almost equality restricts to genuine almost equality on
    every finite-measure test, supporting Federer 2.5.14,
    p. 108. This will be applied to compact supports. *)
Lemma measure_locally_almost_on_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (P A : set X) :
  measure_locally_almost_everywhere mu P -> mu A< +oo -> measure_almost_everywhere_on mu A P.
Proof. by move=> h hA; exact: h A hA. Qed.
