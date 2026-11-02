(** Federer (1969), 3.2.38, pp. 274--275: finite closed cube
    overlaps are null for actual Lebesgue measure, by 2.6.5 and 2.7.16. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes LebesgueScalarMeasure
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_coordinate_hyperplane_null]: supporting
    null boundaries for the cube sums in Federer 3.2.38, p. 275.
    A singleton coordinate has zero scalar length; the coordinate
    product law gives zero even when all other coordinates are unbounded.
    The index i ensures positive ambient dimension without adding a
    separate dimension hypothesis to subsequent cube statements. *)
Lemma euclidean_coordinate_hyperplane_null (R:realType) n (i:'I_n) (b:R):
  @euclidean_lebesgue_measure R n [set x|x i=b]=0%E.
Proof.
pose A j:=if j==i then [set b] else @setT R.
have hA j:measure_measurable (@lebesgue_scalar_measure R) (A j).
  rewrite /A; case:(j==i); last exact:measure_measurable_whole (lebesgue_scalar_is_measure R).
  exact:(@measure_null_measurable R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) [set b] (lebesgue_scalar_singleton b)).
have hCarrier:euclidean_coordinate_box A=[set x:inner_metric_space (@euclidean_inner_productP R n)|x i=b].
  apply/seteqP; split=>x.
  - move=>hx; have h:=hx i; by rewrite /A eqxx in h.
  - move=>hx j; rewrite /A; case:(eqVneq j i)=>[->|hji] //.
have [_ hVolume]:=@euclidean_coordinate_box_measure R n A hA.
have hZero:@euclidean_lebesgue_measure R n (euclidean_coordinate_box A)=0%E.
  by rewrite hVolume (bigD1 i) //= /A eqxx lebesgue_scalar_singleton mul0e.
by rewrite hCarrier in hZero.
Qed.
