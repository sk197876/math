(** Federer (1969), 2.2.3, p. 62, final paragraph: the Borel-superset
    infimum is a Borel regular measure, agreeing with the original measure
    on Borel sets. We prove these consequences from the abstract infimum
    laws. Source context: BorelRegularisationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport MeasureUP MeasureSplit
  MeasureIndexedCover BorelFamilyBasic TopologicalBorel BorelRegularMeasureUP
  BorelRegularisationUP BorelRegularisationBasic BorelRegularisationAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regularisation_is_measure]: Federer
    2.2.3, p. 62, measure laws for the Borel-superset infimum.
    Supporting strengthening: the cover inequality does not require
    Borel measurability for the original measure. Attaining Borel
    supersets and their countable union prove the inequality. *)
Theorem borel_regularisation_is_measure (R : realType) (T : topologicalType)
    (mu nu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu) : is_measure nu.
Proof.
constructor; first by move=> A; exact: (@borel_regularisation_nonnegative R T mu nu hm hr A).
move=> A F hF hc.
pose B C := projT1 (cid (@borel_regularisation_attained R T mu nu hm hr C)).
have hB C : C `<=` B C /\ borel_set (B C) /\ nu C = mu (B C).
  exact: projT2 (cid (@borel_regularisation_attained R T mu nu hm hr C)).
have hU : borel_set (\bigcup_(C in F) B C).
  apply: (@borel_set_countable_union T _ F B hF)=> C _; exact: (hB C).2.1.
have hcover : A `<=` \bigcup_(C in F) B C.
  move=> x hx; have [C hC hxC] := hc x hx; exists C=> //; exact: (hB C).1.
apply: le_trans (@borel_regularisation_lower R T mu nu hr A _ hcover hU) _.
have hb := @measure_indexed_cover R T _ mu hm (\bigcup_(C in F) B C) F B hF
  (fun x hx => hx).
have he : nonnegative_sum F (fun C => mu (B C)) = nonnegative_sum F nu.
  apply: nonnegative_sum_ext=> C _; exact: esym (hB C).2.2.
by rewrite he in hb.
Qed.

(** Source for [borel_regularisation_borel_measurable]: Federer 2.2.3, p.
    62, supporting Borel measurability of the new measure. Split an
    attaining Borel superset by the target Borel set and apply the original
    measurability equation and infimum lower bounds. *)
Theorem borel_regularisation_borel_measurable (R : realType) (T : topologicalType)
    (mu nu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu)
    (hb : forall A, borel_set A -> measure_measurable mu A) A :
  borel_set A -> measure_measurable nu A.
Proof.
move=> hA X; have hn := @borel_regularisation_is_measure R T mu nu hm hr.
apply/eqP; rewrite eq_le (measure_split_upper hn) /=.
have [B [hXB [hB he]]] := @borel_regularisation_attained R T mu nu hm hr X.
rewrite he (hb A hA B); apply: leeD.
- apply: (@borel_regularisation_lower R T mu nu hr (X `&` A) (B `&` A)).
  + move=> x [hx ha]; split=> //; exact: hXB.
  + exact: (@borel_family_binary_intersection _ setT _ (borel_sets_family T) B A hB hA).
- apply: (@borel_regularisation_lower R T mu nu hr (X `\` A) (B `\` A)).
  + move=> x [hx ha]; split=> //; exact: hXB.
  + exact: borel_set_difference hB hA.
Qed.

(** Source for [borel_regularisation_borel_regular]: Federer 2.2.3, p. 62,
    Borel regularity of the infimum measure. The attaining Borel superset
    has unchanged value, and open sets are Borel and measurable. *)
Theorem borel_regularisation_borel_regular (R : realType) (T : topologicalType)
    (mu nu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu) :
  (forall A, borel_set A -> measure_measurable mu A) -> is_borel_regular_measure nu.
Proof.
move=> hb; constructor.
- move=> U hU; apply: (@borel_regularisation_borel_measurable R T mu nu hm hr hb U).
  exact: open_borel_set hU.
- move=> A; have [B [hAB [hB he]]] := @borel_regularisation_attained R T mu nu hm hr A.
  exists B; split=> //; split=> //.
  by rewrite (@borel_regularisation_borel_value R T mu nu hm hr B hB).
Qed.
