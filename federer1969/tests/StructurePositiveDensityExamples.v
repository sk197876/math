(** Federer (1969), 3.3.15, p. 299: actual positive zero
    atom, line interval and original nonmeasurable source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanOpenUnitCube
  EuclideanUnitCubeRectifiable EuclideanLebesgueDimensions OrthogonalProjectionProbability
  EuclideanProjectionSpace StructureConeUP StructurePositiveDensityDecomposition
  FiniteHausdorffPositiveUpperDensity HausdorffMeasure HausdorffClosedCoverAgreement
  RectifiableSetUP MeasureUP MeasureBasic MeasureAlmostUP BorelRegularMeasureUP TopologicalBorel.
From FedererTests Require Import StructureHausdorffStructureExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_positive_density_conclusion]: regression
    notation for the COMPLETE conclusion in Federer 3.3.15, p. 299.
    Retain the original measurable countably measure rectifiable
    part, original pure remainder and its original projected image. *)
Definition structure_positive_density_conclusion (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  exists Q,is_countably_measure_m_rectifiable phi m Q /\measure_measurable phi Q /\
    is_purely_measure_m_unrectifiable phi m (W `\` Q) /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` (W `\` Q))=0].

(** Source for [structure_positive_density_hausdorff_source]: actual
    application support for COMPLETE Federer 3.3.15, p. 299. Actual
    2.10.19(2) discharges positive upper density for EVERY original
    finite Hausdorff source, without assuming source measurability. *)
Lemma structure_positive_density_hausdorff_source (R:realType) n m (hmn:(m<=n)%N)
    (W:set (inner_metric_space (@euclidean_inner_productP R n))):
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  structure_positive_density_conclusion hmn
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W.
Proof.
move=>hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hStructure:is_structure_measure H.
  split; first exact:hH.
  move=>C hC; exact:(borel_regular_borel_measurable hH
    (@hausdorff_measure_borel_regular R [the metricType R of X] m) (closed_borel_set hC)).
exact:(@federer_3_3_15 R n m hmn H W hStructure hFinite
  (@finite_hausdorff_positive_upper_density R [the metricType R of X] m W hFinite)).
Qed.

(** Source for [structure_positive_density_zero_atom]: actual
    positive R^0 unit atom of mass one in COMPLETE Federer 3.3.15,
    p. 299. Keep both zero dimensions and the original conclusion. *)
Example structure_positive_density_zero_atom (R:realType):
  let W:=@euclidean_open_unit_cube R 0 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 in
  H W= 1 /\structure_positive_density_conclusion (leqnn 0) H W.
Proof.
cbn zeta.
have hMass:=(@euclidean_open_unit_cube_measure_rectifiable R 0).2.2.
split; first exact:hMass.
apply:structure_positive_density_hausdorff_source.
by rewrite hMass ltry.
Qed.

(** Source for [structure_positive_density_unit_interval]: actual
    positive open unit line interval of Hausdorff mass one in
    COMPLETE Federer 3.3.15, p. 299. The original ambient measure
    is retained; no finite whole-space mass is a theorem premise. *)
Example structure_positive_density_unit_interval (R:realType):
  let W:=@euclidean_open_unit_cube R 1 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 in
  H W= 1 /\structure_positive_density_conclusion (leqnn 1) H W.
Proof.
cbn zeta.
have hMass:=(@euclidean_open_unit_cube_measure_rectifiable R 1).2.2.
split; first exact:hMass.
apply:structure_positive_density_hausdorff_source.
by rewrite hMass ltry.
Qed.

(** Source for [structure_positive_density_nonmeasurable_source]:
    ACTUAL original nonmeasurable positive finite-mass line source
    from 2.2.4 in COMPLETE Federer 3.3.15, p. 299. The actual
    subcritical density theorem verifies the premise on the original
    source; no measurable hull replaces it in the new theorem. *)
Example structure_positive_density_nonmeasurable_source (R:realType):
  exists W:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) W /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 W< +oo) /\
    structure_positive_density_conclusion (leqnn 1)
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1) W.
Proof.
have [W [hNot [hMass hAll]]]:=@structure_hausdorff_original_nonmeasurable_source R.
exists W; split; first exact:hNot.
split; first exact:hMass.
exact:(@structure_positive_density_hausdorff_source R 1 1 (leqnn 1) W (andP hMass).2).
Qed.
