(** Federer (1969), 3.1.4, pp. 215–216: the property proved on
    the large sets H holds almost everywhere. Finite test sets need
    not themselves be measurable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_large_subsets_almost]: the inference
    from arbitrarily small measure of E minus H to the almost-everywhere
    conclusion in Federer 3.1.4, pp. 215–216, for a fixed finite E. *)
Lemma finite_measure_large_subsets_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E P : set X) :
  is_measure mu ->
  (forall e : R, (0<e)%R -> exists H : set X,
    mu (E `\` H)<e%:E /\ H `<=` P) ->
  measure_almost_everywhere_on mu E P.
Proof.
move=> hm hs; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
apply/lee_addgt0Pr=> e he; rewrite add0e.
have [H [hH hHP]] := hs e he.
apply: le_trans _ (ltW hH).
apply: (measure_mono hm)=> x [hx hn]; split=> //.
by move=> h; apply: hn; exact: hHP.
Qed.

(** Source for [countably_finite_large_subsets_almost]: the passage
    from arbitrary finite E to the full almost-everywhere assertion
    of Federer 3.1.4, p. 214, after the construction on pp. 215–216.
    A countably measurable ambient space supplies the exhaustion. *)
Theorem countably_finite_large_subsets_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A P : set X) :
  is_measure mu -> measure_countably_measurable mu setT ->
  (forall E : set X, E `<=` A -> mu E < +oo ->
    forall e : R, (0<e)%R -> exists H : set X,
      mu (E `\` H)<e%:E /\ H `<=` P) ->
  measure_almost_everywhere_on mu A P.
Proof.
move=> hm hc hs.
have [F [hF hFm]] := (countably_measurable_sequence_iff hm setT).1 hc.
have hn n : mu ((A `&` F n) `\` P)=0.
  apply: (finite_measure_large_subsets_almost hm)=> e he.
  apply: (hs (A `&` F n) _ _ e he).
  - by move=> x [hx _].
  - apply: le_lt_trans _ (hFm n).2.
    apply: (measure_mono hm)=> x [_ hx]; exact hx.
have hunion : mu (\bigcup_n ((A `&` F n) `\` P))=0.
  exact (@measure_null_countable_union R X [the choiceType of (nat : Type)] mu hm setT
    (fun n=>(A `&` F n) `\` P) (countableP _) (fun n _=>hn n)).
change (mu (A `\` P)=0).
apply: (@measure_null_subset R X mu hm (A `\` P)
  (\bigcup_n ((A `&` F n) `\` P)) _ hunion)=> x [hx hp].
have hFx : (\bigcup_n F n) x by rewrite -hF.
have [n _ hnx] := hFx; exists n=> //; by split=> //; split.
Qed.
