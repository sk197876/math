(** Federer (1969), 3.3.10, p. 296: every actual incidence
    product-measurability and finite-cover premise is derived locally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  FiniteCoordinates HomInner HomSpaceTopology GrassmannHomogeneousSpace InnerSpaceCountableBase
  EuclideanGrassmannProbability StructureGrassmannMeasureFacts StructureGrassmannCountableBase
  StructureConeUP StructureProductClosedMeasurable MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure BorelRegularMeasureUP TopologicalBorel ProductMeasure ProductRectangleMeasurability
  SuslinSetUP SuslinMeasurability CountablyMeasurableUP CountablyMeasurableBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_incidence_product_background]: the actual
    product/Suslin measurability and finite rectangle used in Federer
    3.3.10, p. 296, before 2.6.2 Fubini. The ORIGINAL phi need only
    measure closed sets; no Borel regularity, local finiteness or finite
    whole-space mass is assumed. Original Suslin A of finite outer
    mass supplies the actual finite parent rectangle. Every auxiliary
    countable base stays local. *)
Theorem structure_incidence_product_background (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (hStructure:is_structure_measure phi):
  is_suslin_set R A ->phi A< +oo ->
  let W:=grassmann_space (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
    (@coordinate_basisP R (n-m)) (@coordinate_basisP R n) in
  let gamma:=@euclidean_grassmann_probability R n (n-m) (leq_subr m n) in
  let hGamma:=(@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).1 in
  let nu:=product_measure hStructure.1 hGamma in
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)*W),
    is_suslin_set R S ->measure_measurable nu S) /\
  (forall S:set (inner_metric_space (@euclidean_inner_productP R n)*W),
    measure_measurable nu S ->S `<=` (A `*` setT) ->measure_countably_measurable nu S).
Proof.
move=>hA hFinite; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose W:=grassmann_space (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
  (@coordinate_basisP R (n-m)) (@coordinate_basisP R n).
pose gamma:=@euclidean_grassmann_probability R n (n-m) (leq_subr m n).
pose hGamma:=(@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).1.
pose nu:=product_measure hStructure.1 hGamma.
have hNu:is_measure nu:=product_measure_is_measure hStructure.1 hGamma.
have [U hU]:=inner_space_countable_open_base (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [V hV]:=@structure_grassmann_countable_open_base R n (n-m).
have hGammaClosed C:closed C ->measure_measurable gamma C.
  move=>hC; exact:(borel_regular_borel_measurable hGamma
    (@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).2.2 (closed_borel_set hC)).
split.
- move=>S hS; exact:(@structure_product_suslin_measurable R [the topologicalType of X] W
    phi gamma hStructure.1 hGamma U V S hU hV hStructure.2 hGammaClosed hS).
- have hAMeasurable:=@suslin_set_measurable R [the topologicalType of X]
    phi hStructure.1 A hStructure.2 hA.
  have hWhole:=measure_measurable_whole hGamma.
  have hParentMeasurable:=@product_measure_rectangle_measurable R X W phi gamma
    hStructure.1 hGamma A setT hAMeasurable hWhole.
  have hParentBound:=@product_measure_rectangle_bound R X W phi gamma
    hStructure.1 hGamma A setT hAMeasurable hWhole.
  rewrite /gamma (@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).2.1 mule1 in hParentBound.
  have hParentFinite:nu (A `*` setT)< +oo:=le_lt_trans hParentBound hFinite.
  move=>S hS hSub; apply:finite_measurable_set_countably_measurable hS _.
  exact:le_lt_trans (@measure_mono R _ nu hNu _ _ hSub) hParentFinite.
Qed.
