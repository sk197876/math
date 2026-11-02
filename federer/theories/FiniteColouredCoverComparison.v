(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic CountablyClosedFamilyUP
  FiniteCoverMeasureBounds BallCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_coloured_cover_comparison_bound]: supporting
    finite-colour sum estimate in the second proof case of
    Federer 2.9.15, p. 161. Each colour is a countable
    disjointed family inside E with the same cellwise mass
    bound. The finite covering inequality sums the colour
    bounds. In the application the number of colours is
    2 zeta+1 and E is chosen with finite arbitrarily small
    reference mass. Empty finite index types are included. *)
Lemma finite_coloured_cover_comparison_bound (R : realType) (X : choiceType) (I : finType)
    (phi psi : set X -> \bar R) (T E : set X) (G : I -> set (set X)) (c : R) :
  is_measure phi -> is_measure psi -> (0<=c)%R -> phi E< +oo ->
  (forall i, countable (G i)) -> (forall i, set_family_disjoint (G i)) ->
  (forall i S, G i S -> S `<=` E) ->
  (forall i S, G i S -> measure_measurable phi S) ->
  (forall i S, G i S -> psi S<=c%:E*phi S) ->
  T `<=` \bigcup_(i in @setT I) \bigcup_(S in G i) S ->
  psi T<=((#|I|%:R : R)*c)%R%:E*phi E.
Proof.
move=> hphi hpsi hc hE hcount hdis hwithin hmeas hcell hcover.
pose U i := \bigcup_(S in G i) S.
have hcolour i : psi (U i)<=c%:E*phi E.
  exact: (@disjoint_reference_cover_measure_bound R X [the choiceType of set X]
    phi psi (U i) E (G i) idfun idfun c hphi hpsi hc (hcount i)
    (fun x hx => hx) (hwithin i) (hmeas i) (hdis i) (hcell i)).
have hbase := @measure_finite_indexed_cover R X I psi hpsi T U hcover.
have hcmp : (\sum_i psi (U i))<=\sum_(i : I) (c%:E*phi E).
  by apply: lee_sum=> i _; exact: hcolour i.
have hf : phi E \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hphi E)).
have he : phi E=(fine (phi E))%:E by rewrite fineK.
have hsum : (\sum_(i : I) (c%:E*phi E))=((#|I|%:R : R)*c)%R%:E*phi E.
  by rewrite he -!EFinM sumEFin sumr_const cardT mulr_natl mulrnAl.
rewrite hsum in hcmp; exact: le_trans hbase hcmp.
Qed.
