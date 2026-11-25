(** Federer (1969), 3.3.16, pp. 299–300: actual
    replacements and exponent agreement on original positive sources. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanOpenUnitCube EuclideanUnitCubeRectifiable
  EuclideanLebesgueDimensions HausdorffMeasure ExteriorMeasure ProjectionMeasure IntegralGeometricMeasure
  StructureGeometricMeasureStructure StructureIntegralGeometricExponentAgreement
  RectifiableSetUP RectifiableGeometricMeasureEquality MeasureUP MeasureBasic.
From FedererTests Require Import StructureHausdorffStructureExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [all_structure_geometric_replacements]: regression
    notation for all FOUR actual replacements in Federer 3.3.16,
    p. 299, plus the finite-infinity exponent assertion on
    pp. 299–300. The replacement exponent u and final exponent t
    remain independent and each includes infinity. *)
Definition all_structure_geometric_replacements (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  structure_geometric_measure_conclusion hmn
    (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) E /\
  structure_geometric_measure_conclusion hmn (@exterior_diameter_measure R n m) E /\
  structure_geometric_measure_conclusion hmn (@gross_measure R n m) E /\
  (forall u: \bar R,1<=u ->structure_geometric_measure_conclusion hmn
    (@convex_integral_geometric_measure R n m hmn u) E) /\
  forall t: \bar R,1<=t ->@integral_geometric_measure R n m hmn t E=
    @integral_geometric_measure R n m hmn +oo E.

(** Source for [rectifiable_source_all_structure_replacements]:
    actual regression support for COMPLETE Federer 3.3.16,
    pp. 299–300. Actual 3.2.26 computes each original finite
    input mass; then apply all FOUR new complete theorems and
    the new finite-I-infinity exponent theorem to original E. *)
Lemma rectifiable_source_all_structure_replacements (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<m)%N ->is_measure_m_rectifiable
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) m E ->
  all_structure_geometric_replacements hmn E.
Proof.
move=>hm hRect.
have hEqual:=@federer_3_2_26 R m n hmn E hRect.
have hFinite:=hRect.2.
split.
- apply:federer_3_3_16_spherical; by rewrite hEqual.1.
split.
- apply:federer_3_3_16_exterior; by rewrite hEqual.2.1.
split.
- apply:federer_3_3_16_gross; by rewrite hEqual.2.2.1.
split.
- move=>u hu; apply:(@federer_3_3_16_convex_integral R n m hmn E u hm hu).
  by rewrite (hEqual.2.2.2 u hu).1.
- move=>t ht; apply:(@federer_3_3_16_exponent_agreement R n m hmn E t _ ht).
  by rewrite (hEqual.2.2.2 +oo (leey 1)).2.
Qed.

(** Source for [structure_replacement_positive_unit_interval]:
    actual positive unit line interval of H^1 mass one in
    COMPLETE Federer 3.3.16, pp. 299–300. Retain every
    replacement, independent Q_u exponent, original pure remainder,
    both equality-criterion directions and every final exponent. *)
Example structure_replacement_positive_unit_interval (R:realType):
  let E:=@euclidean_open_unit_cube R 1 in
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 E= 1 /\
  all_structure_geometric_replacements (leqnn 1) E.
Proof.
cbn zeta.
have h:=@euclidean_open_unit_cube_measure_rectifiable R 1.
split; first exact:h.2.2.
exact:(@rectifiable_source_all_structure_replacements R 1 1 (leqnn 1) _ (ltnSn 0) h.1).
Qed.

(** Source for [structure_replacement_positive_zero_atom]: actual
    positive R^0 unit atom in the natural-degree spherical/Gross
    extensions of Federer 3.3.16, p. 299. Both complete structure
    conclusions and all exponent values remain. The printed Q_u
    definition keeps its positive-degree convention separately. *)
Example structure_replacement_positive_zero_atom (R:realType):
  let E:=@euclidean_open_unit_cube R 0 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 in
  H E= 1 /\
  structure_geometric_measure_conclusion (leqnn 0)
    (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0) E /\
  structure_geometric_measure_conclusion (leqnn 0) (@gross_measure R 0 0) E /\
  forall t: \bar R,1<=t ->@integral_geometric_measure R 0 0 (leqnn 0) t E= 1.
Proof.
cbn zeta.
have h:=@euclidean_open_unit_cube_measure_rectifiable R 0.
have hEqual:=@federer_3_2_26 R 0 0 (leqnn 0) _ h.1.
split; first exact:h.2.2.
split.
- apply:federer_3_3_16_spherical; by rewrite hEqual.1 h.2.2 ltry.
split.
- apply:federer_3_3_16_gross; by rewrite hEqual.2.2.1 h.2.2 ltry.
- move=>t ht; by rewrite (hEqual.2.2.2 t ht).2 h.2.2.
Qed.

(** Source for [structure_replacement_original_nonmeasurable_source]:
    ACTUAL original nonmeasurable positive finite-mass line source
    from 2.2.4 in COMPLETE Federer 3.3.16, pp. 299–300.
    Actual 3.3.13 verifies its finite Hausdorff rectifiability,
    actual 3.2.26 computes every original replacement mass, and
    the FOUR new complete theorems retain the unchanged source. *)
Example structure_replacement_original_nonmeasurable_source (R:realType):
  exists E:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) E /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 E< +oo) /\
    all_structure_geometric_replacements (leqnn 1) E.
Proof.
have [E [hNot [hMass hAll]]]:=@structure_hausdorff_original_nonmeasurable_source R.
have hRect:is_measure_m_rectifiable
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1) 1 E.
  apply:((hAll 1 (lexx 1)).1.2).1; exact:esym (hAll 1 (lexx 1)).2.
exists E; split; first exact:hNot.
split; first exact:hMass.
exact:(@rectifiable_source_all_structure_replacements R 1 1 (leqnn 1) E (ltnSn 0) hRect).
Qed.
