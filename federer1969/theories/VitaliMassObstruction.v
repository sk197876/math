(** Supporting obstruction for Federer (1969), 2.8.20, p. 152. The book
    cites Caratheodory, Vorlesungen ueber reelle Funktionen, second edition
    (1927), pp. 689–692, for the Bohr rectangle counterexample. Saks, Remark
    on the differentiability of the Lebesgue indefinite integral, Fundamenta
    Mathematicae 22 (1934), Lemma B, pp. 258–259, gives small-integral
    functions with large averages on small rectangles through every point.
    Cesari, Sul teorema di densita in senso forte, Ann. Scuola Norm. Sup.
    Pisa (2) 8 (1939), section II.4, pp. 306–307, expands this route. The
    abstract mass comparison below supports that route; it is not asserted
    to occur verbatim in these sources and does not by itself construct the
    required rectangle family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover MeasureDisjointSupport
  NonnegativeSum NonnegativeSumScale CoveringRelationUP CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_remainder_measure_cover_bound]: supporting
    outer-measure comparison for the non-Vitali assertion in
    Federer 2.8.20, p. 152. A set whose uncovered
    remainder is null has measure at most that of the covering
    union, without requiring either set to be measurable. *)
Lemma null_remainder_measure_cover_bound (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A U : set X) :
  is_measure phi -> phi (A `\` U) = 0 -> phi A <= phi U.
Proof.
move=> hm hz.
have hc : A `<=` (A `\` U) `|` U.
  move=> x hx; case: (pselect (U x))=> [hu|hn]; [by right|left; by split].
have h := @measure_binary_cover R X phi hm A (A `\` U) U hc.
by rewrite hz add0e in h.
Qed.

(** Source for [vitali_fine_mass_obstruction]: supporting
    contradiction for Federer 2.8.20, p. 152, using
    the large-average construction in Saks1934 Lemma B,
    pp. 258–259, and Cesari1939 section II.4, pp. 306–307.
    A fine subrelation whose members carry at least p times
    their phi mass in a second measure cannot have an
    almost-covering disjoint selection if that second measure's
    total mass is smaller than p times the target's phi mass.
    The second measure need only make these members measurable. *)
Theorem vitali_fine_mass_obstruction (R : realType) (X : metricType R)
    (phi nu : set X -> \bar R) (V C : X -> set X -> Prop)
    (Z : set X) (p : R) :
  is_measure phi -> is_measure nu -> (0 < p)%R ->
  (forall x S, C x S -> V x S) ->
  (forall x, Z x -> covering_relation_fine_at C x) ->
  (forall S, covering_relation_image C Z S -> measure_measurable nu S) ->
  (forall S, covering_relation_image C Z S -> p%:E * phi S <= nu S) ->
  nu setT < p%:E * phi Z -> ~ is_vitali_relation phi V.
Proof.
move=> hm hn hp hCV hf hmeas hmass hstrict hv.
have [G [hG [hc [hd hz]]]] := @vitali_relation_selection R X phi V hv C Z hCV hf.
pose U := \bigcup_(S in G) S.
have hZU : phi Z <= phi U := @null_remainder_measure_cover_bound R X phi Z U hm hz.
have hU : phi U <= nonnegative_sum G phi.
  exact (@measure_indexed_cover R X [the choiceType of set X] phi hm U G idfun hc (fun _ h => h)).
have h0p : 0 <= p%:E by rewrite lee_fin; exact: ltW hp.
have hscale : p%:E * phi Z <= p%:E * nonnegative_sum G phi.
  apply: lee_wpmul2l; first exact h0p.
  exact: le_trans hZU hU.
have hsum : nonnegative_sum G (fun S => p%:E * phi S) <= nonnegative_sum G nu.
  apply: nonnegative_sum_mono=> S hS; exact: hmass S (hG S hS).
have htotal : nonnegative_sum G nu <= nu setT.
  apply: (@measure_disjoint_sum_bound R X [the choiceType of set X] nu hn setT G idfun).
  - by move=> S hS x hx.
  - move=> S hS; exact: hmeas S (hG S hS).
  - exact hd.
rewrite -(@nonnegative_sum_scale R [the choiceType of set X] G phi p (ltW hp)
  (fun S _ => measure_nonnegative hm S)) in hscale.
have hbad := le_lt_trans (le_trans hscale (le_trans hsum htotal)) hstrict.
by rewrite ltxx in hbad.
Qed.
