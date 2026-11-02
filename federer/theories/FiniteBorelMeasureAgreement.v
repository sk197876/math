(** Supporting Federer (1969), 2.10.46, p. 204: two Borel regular measures
    with equal finite total mass agree everywhere if one dominates the
    other. Split into a Borel set and its complement by 2.1.3(3), pp. 54–55,
    then use the Borel hull law of 2.2.3, p. 61. This finite comparison is
    used after restricting the product argument to finite rectangles. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP BorelMeasureAgreement TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_dominated_borel_regular_measures_agree]:
    supporting finite-total-mass comparison in the arbitrary-set
    product argument of 2.10.46, p. 204. Equality
    is proved on Borel sets first and extended by hulls. *)
Theorem finite_dominated_borel_regular_measures_agree (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) :
  is_measure mu -> is_measure nu -> is_borel_regular_measure mu -> is_borel_regular_measure nu ->
  (forall A, mu A<=nu A) -> mu setT=nu setT -> nu setT< +oo -> mu=nu.
Proof.
move=> hm hn hr hs hdom htot hfin.
apply: (borel_regular_measures_agree hm hn hr hs)=> A hA.
have hcfin : nu (~` A) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hn _)).
  exact: le_lt_trans (measure_mono hn (@subsetT _ _)) hfin.
have hmfin : mu (~` A) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  exact: le_lt_trans (hdom _) (le_lt_trans (measure_mono hn (@subsetT _ _)) hfin).
have hmu := borel_regular_borel_measurable hm hr hA setT.
have hnu := borel_regular_borel_measurable hn hs hA setT.
rewrite setTI setTD in hmu hnu.
have hem : mu A=mu setT-mu (~` A) by rewrite hmu addeK.
have hen : nu A=nu setT-nu (~` A) by rewrite hnu addeK.
apply/eqP; rewrite eq_le (hdom A) /= hem hen htot.
apply: leeD=> //; by rewrite leeN2.
Qed.
