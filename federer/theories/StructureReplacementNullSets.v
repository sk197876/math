(** Federer (1969), 3.3.16, p. 299: null sets for
    the replacement measure are null for every integral-geometric exponent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureReplacementMeasureUP
  EuclideanProjectionSpace EuclideanLebesgueDimensions OrthogonalProjectionProbability
  IntegralGeometricMeasure IntegralGeometricNullSets MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_replacement_null_integral_geometric]:
    null remainder comparison needed in Federer 3.3.16, p. 299.
    An actual equal-mass Borel hull remains null for the original
    replacement measure. Independent projection domination makes
    EVERY original projection null on that hull. Actual 2.10.5
    gives nullity for each integral-geometric exponent, including
    infinity; no nonmeasurable hull difference is declared null. *)
Lemma structure_replacement_null_integral_geometric (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  is_structure_replacement_measure m phi ->phi A=0 ->1<=t ->
  @integral_geometric_measure R n m hmn t A=0.
Proof.
move=>hLaws hZero ht.
have [B [hAB [hB hMass]]]:=borel_regular_cover (structure_replacement_borel_regular hLaws) A.
have hBZero:phi B=0 by rewrite -hMass.
have [c [hc hBound]]:=structure_replacement_projection_bound hLaws.
apply:(@integral_geometric_projection_null_iff R n m hmn t A ht).2.
exists B; split; first exact:hAB.
split; first exact:hB.
have hTheta:=theta_star_is_measure R hmn.
apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta))=>p _.
have h:=hBound B p; rewrite hBZero mule0 in h.
apply/eqP; rewrite eq_le (measure_nonnegative (euclidean_lebesgue_is_measure R m)) andbT.
  exact:h.
Qed.
