(** Federer (1969), 2.5.10, p. 101: supporting almost comparisons for the
    restricted measures. The conventions are 2.1.2, p. 54, and 2.3.1, p. 72. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [restricted_almost_everywhere_iff]: supporting exact
    relative almost convention for Federer 2.5.10, p. 101;
    no measurability of the restricting set or predicate is needed. *)
Lemma restricted_almost_everywhere_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (B P : set X) :
  measure_almost_everywhere (measure_restrict mu B) P <->
  measure_almost_everywhere mu [set x | B x -> P x].
Proof.
rewrite /measure_almost_everywhere /measure_restrict.
have he : ~` [set x | B x -> P x]=B `&` (~` P).
  apply/seteqP; split.
  - move=> x hn; split.
    + apply: contrapT=> hb; apply: hn=> hx; exfalso; exact: hb hx.
    + move=> hp; apply: hn=> _; exact: hp.
  - move=> x [hb hp] h; exact: hp (h hb).
by rewrite he.
Qed.

(** Source for [almost_everywhere_for_restricted_measure]: supporting
    inheritance of almost assertions in Federer 2.5.10, p. 101,
    from the null-subset law of 2.1.3(6), p. 55. *)
Lemma almost_everywhere_for_restricted_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B P : set X) :
  measure_almost_everywhere mu P -> measure_almost_everywhere (measure_restrict mu B) P.
Proof.
move=> hp; apply: (@measure_null_subset R X mu hm _ _ _ hp).
by move=> x [_ hx].
Qed.
