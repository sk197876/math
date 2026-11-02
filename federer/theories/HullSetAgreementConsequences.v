(** Null-set bookkeeping in Federer (1969), 2.9.11, p. 158: transfer a hull
    to an intermediate measurable set differing only on a null set. The
    lemmas use the existing measure, null-modification and hull laws; no
    regularity is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureHull MeasureSplit MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasureHullNullTransfer MeasurableAlmostModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_hull_remainder_null]: supporting measurable-set
    case of Federer 2.9.11, p. 158 A hull of a measurable set has null
    remainder, by its test law on the measurable complement. No
    finite-total-mass cancellation is needed. *)
Lemma measurable_hull_remainder_null (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B : set X) :
  is_measure phi -> is_measure_hull phi A B -> measure_measurable phi A -> phi (B `\` A)=0.
Proof.
move=> hm hB hA.
have hcomp := @measure_measurable_complement R X phi A hA.
have ht := @measure_hull_test R X phi A B hB (~` A) hcomp.
have he0 : (~` A) `&` A=set0.
  apply/seteqP; split=> x; [by move=> [hn ha]; exact: hn ha|by move=> []].
have heB : (~` A) `&` B=B `\` A by rewrite setIC setDE.
by move: ht; rewrite he0 heB (measure_empty hm)=> ->.
Qed.

(** Source for [hull_set_agreement_consequences]: supporting set-theoretic
    conclusion of the P argument in Federer 2.9.11, p. 158 An arbitrary A
    lies in its hull B and P is measurable and almost equal to B. Then A
    minus P is null, A union P is a hull, and A is measurable exactly when P
    minus A is null. *)
Theorem hull_set_agreement_consequences (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B P : set X) :
  is_measure phi -> is_measure_hull phi A B -> measure_measurable phi P ->
  measure_almost_everywhere phi [set x | P x <-> B x] ->
  phi (A `\` P)=0 /\ is_measure_hull phi A (A `|` P) /\
    (measure_measurable phi A <-> phi (P `\` A)=0).
Proof.
move=> hm hB hP he.
have hAB := @measure_hull_subset R X phi A B hB.
have hAP : phi (A `\` P)=0.
  apply: (@measure_null_subset R X phi hm _ (~` [set x | P x <-> B x])) he.
  move=> x [ha hnp] hx; exact: hnp (hx.2 (hAB x ha)).
have hPB := @measure_agreeing_sets_difference_null R X phi P B hm he.
have hBC : measure_almost_everywhere phi [set x | B x <-> (A `|` P) x].
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ he)=> x hx; split.
  - move=> hb; right; exact: hx.2 hb.
  - by move=> [ha|hp]; [exact: hAB x ha|exact: hx.1 hp].
have hhull := @measure_hull_agreement_transfer R X phi A B (A `|` P) hm hB
  (fun x hx => or_introl hx) hBC.
split=> //; split=> //; split.
- move=> hA.
  have hBA := @measurable_hull_remainder_null R X phi A B hm hB hA.
  have hz := @measure_null_union R X phi hm (P `\` B) (B `\` A) hPB hBA.
  apply: (@measure_null_subset R X phi hm (P `\` A) _) hz.
  move=> x [hp hnA]; case: (pselect (B x))=> hb.
  + right; by split.
  + left; by split.
- move=> hPA.
  have hz := @measure_null_union R X phi hm (A `\` P) (P `\` A) hAP hPA.
  apply: (@measurable_set_null_modification R X phi hm P A _ hz _ hP)=> x hn.
  split.
  + move=> hp; apply: contrapT=> hna; apply: hn; right; by split.
  + move=> ha; apply: contrapT=> hnp; apply: hn; left; by split.
Qed.
