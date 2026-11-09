(** Federer (1969), 3.3.10, p. 296: both ORIGINAL
    product-nullity assertions and the actual Grassmann almost statement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric FiniteCoordinates
  HomInner HomSpaceTopology GrassmannHomogeneousSpace EuclideanGrassmannProbability
  StructureGrassmannMeasureFacts StructureConeUP StructurePlaneGrowth StructureProjectionKernel
  StructureKernelOnto StructureIncidenceSets StructureIncidenceSuslin StructureIncidenceProductBackground
  StructureFixedProjectionAssertions StructureTrichotomy StructureProductNullSections
  RectifiableSetUP SuslinSetUP SuslinMeasurability MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic ProductMeasure ProductSections
  ProductRectangleMeasurability CountablyMeasurableUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_incidence_product_null]: the two original
    product computations and final Grassmann Fubini computation in
    Federer 3.3.10, p. 296. All incidence measurability, actual finite
    parent and countable-measurability premises are proved. The
    original A and S_i remain unchanged; no ordinary infinite
    derivative, measurable hull difference or structure conclusion
    is added as a hypothesis. *)
Theorem structure_incidence_product_null (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (hStructure:is_structure_measure phi):
  is_purely_measure_m_unrectifiable phi m A ->is_suslin_set R A ->phi A< +oo ->
  let gamma:=@euclidean_grassmann_probability R n (n-m) (leq_subr m n) in
  let hGamma:=(@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).1 in
  let nu:=product_measure hStructure.1 hGamma in
  let S1:=@structure_first_incidence R n m phi A in
  let S2:=@structure_second_incidence R n m phi A in
  let S3:=@structure_third_incidence R n m A in
  let D:=(A `*` setT) `\` (S2 `|` S3) in
  nu S1=0 /\nu D=0 /\
  measure_almost_everywhere gamma [set V|phi (product_horizontal_section D V)=0].
Proof.
move=>hPure hA hFinite; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose W:=grassmann_space (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
  (@coordinate_basisP R (n-m)) (@coordinate_basisP R n).
pose gamma:=@euclidean_grassmann_probability R n (n-m) (leq_subr m n).
pose hGamma:=(@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).1.
pose nu:=product_measure hStructure.1 hGamma.
pose S1:=@structure_first_incidence R n m phi A.
pose S2:=@structure_second_incidence R n m phi A.
pose S3:=@structure_third_incidence R n m A.
pose D:=(A `*` setT) `\` (S2 `|` S3).
pose E:=(A `*` setT) `\` (S1 `|` (S2 `|` S3)).
have hNu:is_measure nu:=product_measure_is_measure hStructure.1 hGamma.
have [hSuslin1 [hSuslin2 hSuslin3]]:=@structure_incidence_sets_suslin R n m hmn phi A hStructure hA.
have [hSuslinMeasurable hCountably]:=@structure_incidence_product_background R n m phi A hStructure hA hFinite.
have hMeasurable1:measure_measurable nu S1:=hSuslinMeasurable S1 hSuslin1.
have hMeasurable2:measure_measurable nu S2:=hSuslinMeasurable S2 hSuslin2.
have hMeasurable3:measure_measurable nu S3:=hSuslinMeasurable S3 hSuslin3.
have hMeasurableParent:measure_measurable nu (A `*` setT).
  have hAMeasurable:=@suslin_set_measurable R [the topologicalType of X] phi hStructure.1 A hStructure.2 hA.
  exact:(@product_measure_rectangle_measurable R X W phi gamma hStructure.1 hGamma
    A setT hAMeasurable (measure_measurable_whole hGamma)).
have hMeasurable23:=measure_measurable_union hNu hMeasurable2 hMeasurable3.
have hMeasurable123:=measure_measurable_union hNu hMeasurable1 hMeasurable23.
have hMeasurableD:measure_measurable nu D.
  rewrite /D setDE; exact:(measure_measurable_intersection hNu hMeasurableParent
    (measure_measurable_complement hMeasurable23)).
have hMeasurableE:measure_measurable nu E.
  rewrite /E setDE; exact:(measure_measurable_intersection hNu hMeasurableParent
    (measure_measurable_complement hMeasurable123)).
have hCountably1:measure_countably_measurable nu S1.
  apply: (hCountably S1 hMeasurable1).
  move=>[a V] [ha _]; by split.
have hCountablyD:measure_countably_measurable nu D.
  apply: (hCountably D hMeasurableD).
  by move=>z [hz _].
have hCountablyE:measure_countably_measurable nu E.
  apply: (hCountably E hMeasurableE).
  by move=>z [hz _].
have hNull1:nu S1=0.
  apply:(@structure_product_null_horizontal_sections R X W phi gamma hStructure.1 hGamma S1 hCountably1)=>V.
  have [p hKernel]:=@structure_projection_kernel_onto R n m hmn V.
  change (phi [set a:X|S1 (a,V)]=0).
  rewrite -hKernel.
  exact:(@structure_first_projection_section_null R n m hmn phi A p hStructure hPure).
have hNullE:nu E=0.
  apply:(@structure_product_null_vertical_sections R X W phi gamma hStructure.1 hGamma E hCountablyE)=>a.
  case:(pselect (A a))=>ha.
  - have hTrichotomy:=@structure_trichotomy R n m hmn phi A a hStructure hA.
    have hSection:product_vertical_section E a=
        ~` [set V:W|structure_plane_trichotomy m phi A a V].
      apply/seteqP; split=>V;
        rewrite /product_vertical_section /E /S1 /S2 /S3
          /structure_first_incidence /structure_second_incidence /structure_third_incidence
          /structure_plane_trichotomy /=; tauto.
    by rewrite hSection.
  - have hSection:product_vertical_section E a=set0.
      apply/seteqP; split; last by [].
      by move=>V [[hA0 _] _]; exfalso; exact:ha hA0.
    rewrite hSection; exact:measure_empty hGamma.
have hNullD:nu D=0.
  have hUnionNull:=measure_null_union hNu hNull1 hNullE.
  apply:(@measure_null_subset R [the choiceType of (X*W)%type] nu hNu D (S1 `|` E) _ hUnionNull).
  move=>z [hParent hNo23]; case:(pselect (S1 z))=>hFirst.
  - by left.
  - right; split; first exact:hParent.
    by move=>[h1|h23]; [exact:hFirst h1|exact:hNo23 h23].
split; first exact:hNull1.
split; first exact:hNullD.
exact:(@structure_product_null_horizontal_almost R X W phi gamma hStructure.1 hGamma D hCountablyD hNullD).
Qed.
