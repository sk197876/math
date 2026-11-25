(** Federer (1969), 3.3.10, p. 296: all three fixed-
    projection assertions for the ORIGINAL incidence sections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureProjectionKernel StructurePlaneGrowth StructurePlaneCostOrder
  StructureIncidenceSets StructurePureZeroGrowth StructureInfiniteProjectionNull
  StructureAffineFibreInfinite EuclideanLebesgueDimensions RectifiableSetUP PureUnrectifiableLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_first_projection_section_null]: the first
    fixed-projection assertion of Federer 3.3.10, p. 296. The
    original section is a pure subset of A; the original ordinary
    zero growth for A is inherited by that section. Actual 3.3.8
    then gives its original outer mass zero. No section-measurability
    or finite-mass hypothesis is needed for this part. *)
Theorem structure_first_projection_section_null (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m A ->
  phi [set a:inner_metric_space (@euclidean_inner_productP R n)|
    @structure_first_incidence R n m phi A (a,structure_projection_kernel hmn p)]=0%E.
Proof.
move=>hStructure hPure.
pose B:set (inner_metric_space (@euclidean_inner_productP R n)):=
  [set a|@structure_first_incidence R n m phi A (a,structure_projection_kernel hmn p)].
have hBA:B `<=` A by move=>a [ha _].
have hPureB:=pure_unrectifiable_subset hBA hPure.
apply:(@federer_3_3_8 R n m hmn phi B p hStructure hPureB)=>a [ha hGrowth].
exact:(@structure_plane_zero_growth_subset R n (n-m) m phi B A a
  (structure_projection_kernel hmn p) hStructure.1 hBA hGrowth).
Qed.

(** Source for [structure_second_projection_section_null]: the
    second fixed-projection assertion of Federer 3.3.10, p. 296.
    Actual 3.3.9 is applied to ORIGINAL source A and original
    second section B, whose defining growth condition still uses
    A. The original projected section has Lebesgue outer mass zero. *)
Theorem structure_second_projection_section_null (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->(phi A< +oo)%E ->
  euclidean_lebesgue_measure m (euclidean_projection_linear p @`
    [set a:inner_metric_space (@euclidean_inner_productP R n)|
      @structure_second_incidence R n m phi A (a,structure_projection_kernel hmn p)])=0%E.
Proof.
move=>hStructure hFinite.
apply:(@federer_3_3_9 R n m hmn phi A _ p hStructure hFinite).
by move=>a [_ hGrowth].
Qed.

(** Source for [structure_third_projection_section_infinite]: the
    third fixed-projection assertion of Federer 3.3.10, p. 296.
    The original S3 section projects only to infinite ORIGINAL
    A fibres, by actual punctured affine-fibre accumulation. *)
Theorem structure_third_projection_section_infinite (R:realType) n m (hmn:(m<=n)%N)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  (euclidean_projection_linear p @`
    [set a:inner_metric_space (@euclidean_inner_productP R n)|
      @structure_third_incidence R n m A (a,structure_projection_kernel hmn p)]) `<=`
  [set y|~finite_set (A `&` euclidean_projection_linear p @^-1` [set y])].
Proof. exact:structure_accumulation_projection_infinite_fibre. Qed.
