(** Federer (1969), 3.2.22(2), p. 258: when
    m=mu the fibres have degree zero. Finite H^0
    mass is finite cardinality by 2.10.2, p. 171,
    giving the zero-rectifiable convention of 3.2.14. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffCountingMeasure CountingMeasure
  RectifiableSetUP RectifiableElementary MeasureUP MeasureBasic MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_hausdorff_zero_rectifiable]: supporting
    m=mu boundary of Federer 3.2.22(2), p. 258.
    A set of finite H^0 mass is finite and
    therefore zero rectifiable in the printed convention
    3.2.14, p. 252. It supplies its own exact
    countable cover, with no discarded positive-mass points. *)
Lemma finite_hausdorff_zero_rectifiable (R:realType) (X:metricType R) (E:set X):
  @hausdorff_measure R X 0 E< +oo ->
  is_measure_m_rectifiable (@hausdorff_measure R X 0) 0 E.
Proof.
move=>hMass.
have hFinite:finite_set E.
  apply:contrapT=>hNot.
  have hInf:@hausdorff_measure R X 0 E=+oo.
    rewrite hausdorff_zero_counting_measure.
    have hCount:=@counting_measure_infinite R X E hNot.
    exact hCount.
  by rewrite hInf ltxx in hMass.
split; last exact hMass; split; first exact:hausdorff_measure_is_measure.
exists E; split; first exact:(@rectifiable_countably_rectifiable R X 0 E hFinite).
by rewrite /measure_almost_included setDv (measure_empty (@hausdorff_measure_is_measure R X 0)).
Qed.
