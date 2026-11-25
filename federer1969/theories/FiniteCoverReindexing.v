(** Federer (1969), 2.5.10, p. 101: indexing the finite-measure closed
    family by a well-ordered cardinal representative. This supporting lemma
    replaces an injection of the original indices by an actual family on the
    target; unused indices are assigned the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic MeasureFiniteClosure
  FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_cover_reindexing]: supporting
    transfer of the covering family in Federer 2.5.10,
    p. 101. An injective indexing preserves its finite measurable
    members and countable almost-covering property; it need not
    exhaust the new carrier. This proves existence of the reindexed
    family, with no additional measure assumption. *)
Lemma finite_measure_cover_reindexing (R : realType) (X I J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set I) (C : set J)
    (B : I -> set X) (f : I -> J) :
  set_fun D C f -> set_inj D f ->
  (forall i, D i -> measure_measurable mu (B i) /\ mu (B i) < +oo) ->
  finite_measure_sets_countably_covered mu D B ->
  exists H : J -> set X,
    (forall j, C j -> measure_measurable mu (H j) /\ mu (H j) < +oo) /\
    finite_measure_sets_countably_covered mu C H.
Proof.
move=> hf hinj hB hc.
pose H j := if pselect (exists i, D i /\ f i=j) is left h
  then B (projT1 (cid h)) else set0.
have he i : D i -> H (f i)=B i.
  move=> hi; rewrite /H; case: pselect=> [hh|hn].
  - have [hd heq] := projT2 (cid hh).
    have eqi : projT1 (cid hh) = i := hinj _ _ (mem_set hd) (mem_set hi) heq.
    by rewrite eqi.
  - exfalso; apply: hn; exists i; by split.
exists H; split.
- move=> j _; rewrite /H; case: pselect=> [hh|hn].
  + exact: hB _ (projT2 (cid hh)).1.
  + split; first exact: measure_measurable_empty hm.
    rewrite (measure_empty hm); exact: ltry.
- move=> T hT; have [F [hFD [hF hcov]]] := hc T hT.
  exists (f @` F); split.
  + move=> j [i hi <-]; exact (hf i (hFD i hi)).
  + split; first exact: sub_countable (card_image_le _ _) hF.
    apply: (@measure_null_subset R X mu hm _ _ _ hcov)=> x [hx hn]; split=> //.
    move=> [i hi hxi]; apply: hn; exists (f i); first by exists i.
    by rewrite (he i (hFD i hi)).
Qed.
