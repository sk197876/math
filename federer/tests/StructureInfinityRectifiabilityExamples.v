(** Federer (1969), 3.3.14, p. 298: actual positive unit
    atoms, intervals and original nonmeasurable finite-mass sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanOpenUnitCube EuclideanLebesgueDimensions
  HausdorffMeasure IntegralGeometricMeasure StructureInfinityRectifiability RectifiableSetUP MeasureUP.
From FedererTests Require Import StructureHausdorffStructureExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_infinity_unit_cube]: actual regression
    support for COMPLETE Federer 3.3.14, p. 298. The actual original
    unit cube has I-infinity mass one by the proved 3.3.13 example;
    apply the complete new theorem in every natural dimension. *)
Lemma structure_infinity_unit_cube (R:realType) m:
  let E:=@euclidean_open_unit_cube R m in
  let I:=@integral_geometric_measure R m m (leqnn m) +oo in
  I E= 1 /\is_measure_m_rectifiable I m E.
Proof.
cbn zeta.
have hMass:=((@structure_complete_unit_cube R m).2 +oo (leey 1)).2.
split; first exact:hMass.
apply:(@federer_3_3_14 R m m (leqnn m) (@euclidean_open_unit_cube R m)).
by rewrite hMass ltry.
Qed.

(** Source for [structure_infinity_positive_zero_atom]: actual
    positive R^0 unit cube in COMPLETE Federer 3.3.14, p. 298.
    Keep both zero dimensions and actual I-infinity mass one. *)
Example structure_infinity_positive_zero_atom (R:realType):
  let E:=@euclidean_open_unit_cube R 0 in
  let I:=@integral_geometric_measure R 0 0 (leqnn 0) +oo in
  I E= 1 /\is_measure_m_rectifiable I 0 E.
Proof. exact:structure_infinity_unit_cube. Qed.

(** Source for [structure_infinity_positive_unit_interval]: actual
    open unit line interval in COMPLETE Federer 3.3.14, p. 298.
    Its actual I-infinity mass is one; the theorem gives original
    measure rectifiability without a supplied projection condition. *)
Example structure_infinity_positive_unit_interval (R:realType):
  let E:=@euclidean_open_unit_cube R 1 in
  let I:=@integral_geometric_measure R 1 1 (leqnn 1) +oo in
  I E= 1 /\is_measure_m_rectifiable I 1 E.
Proof. exact:structure_infinity_unit_cube. Qed.

(** Source for [structure_infinity_original_nonmeasurable_source]:
    ACTUAL nonmeasurable positive finite-mass original line source
    from 2.2.4 in COMPLETE Federer 3.3.14, p. 298. Actual 3.3.13
    identifies its original I-infinity and Hausdorff mass; apply the
    new complete theorem without replacing E by a measurable hull. *)
Example structure_infinity_original_nonmeasurable_source (R:realType):
  exists E:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) E /\
    (0<@integral_geometric_measure R 1 1 (leqnn 1) +oo E< +oo) /\
    is_measure_m_rectifiable (@integral_geometric_measure R 1 1 (leqnn 1) +oo) 1 E.
Proof.
have [E [hNot [hMass hAll]]]:=@structure_hausdorff_original_nonmeasurable_source R.
have hEqual:=(hAll +oo (leey 1)).2.
have hFinite:@integral_geometric_measure R 1 1 (leqnn 1) +oo E< +oo.
  rewrite hEqual; exact:(andP hMass).2.
exists E; split; first exact:hNot.
split; first by rewrite hEqual.
exact:(@federer_3_3_14 R 1 1 (leqnn 1) E hFinite).
Qed.
