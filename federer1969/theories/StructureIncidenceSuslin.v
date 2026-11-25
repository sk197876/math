(** Federer (1969), 3.3.10, p. 296: the ORIGINAL three
    incidence sets are Suslin, by their actual kernel lifts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  FiniteCoordinates HomInner HomSpaceTopology GrassmannHomogeneousSpace
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanMetricCompleteness EuclideanMetricSeparability
  MetricProductBackground MetricProductCompleteness MetricProductSeparability CompleteMetricUP
  RealMetricBackground TopologicalProductMaps AffineGroupTopology
  SuslinSetUP SuslinPreimages BorelSuslinImages BorelClosedProjection BorelImageMeasurability
  StructureConeUP StructurePlaneGrowth StructureProjectionKernel StructureKernelOnto StructureKernelTopology
  StructureProjectionAlternativesBorel StructureFibreAccumulation StructureFibreSuslin StructureIncidenceSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_kernel_lift_suslin]: the transfer of
    3.3.2–3.3.3 to the original Grassmann incidence sets used in
    Federer 3.3.10, p. 296. The actual complete separable centre/
    projection space maps continuously onto the actual centre/plane
    space. Kernel surjectivity identifies the exact original image;
    no Borel selector or chosen frame is a new global object. *)
Theorem structure_kernel_lift_suslin (R:realType) n m (hmn:(m<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n)*
      grassmann_space (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
        (@coordinate_basisP R (n-m)) (@coordinate_basisP R n))):
  is_suslin_set R [set z:inner_metric_space (@euclidean_inner_productP R n)*
      euclidean_projection_space R n m|S (z.1,structure_projection_kernel hmn z.2)] ->
  is_suslin_set R S.
Proof.
move=>hLift.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=orthogonal_projection_metric_space R n m.
pose Q:=[the metricType R of metric_product X P].
pose W:=grassmann_space (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
  (@coordinate_basisP R (n-m)) (@coordinate_basisP R n).
pose T:=(X*W)%type.
pose F:Q->T:=fun z=>(z.1,structure_projection_kernel hmn z.2).
have hComplete:is_complete_metric_space Q:=@complete_metric_product R X P
  (@euclidean_metric_complete R n) (@orthogonal_projection_metric_complete R n m).
have hSeparable:exists D:set Q,countable D /\dense D:=@separable_metric_product R X P
  (@euclidean_metric_separable R n) (@orthogonal_projection_metric_separable R n m).
have hHausdorff:hausdorff_space T.
  apply:product_hausdorff; first exact:metric_hausdorff.
  exact:(@grassmann_space_hausdorff R (R_n R (n-m)) (R_n R n)
    (@euclidean_inner_product R (n-m)) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
    (n-m)%N (@coordinate_basis R (n-m)) n (@coordinate_basis R n)
    (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)).
have hKernel:=(@structure_projection_kernel_continuous_open R n m hmn).1.
have hContinuous:continuous F.
  apply:topological_pair_continuous; first exact:first_projection_continuous.
  move=>z; exact:continuous_comp (@second_projection_continuous X P z) (hKernel z.2).
have hImage:F @` [set z:Q|S (F z)]=S.
  apply/seteqP; split.
  - by move=>t [z hz <-].
  - move=>[a V] hS; have [p hP]:=@structure_projection_kernel_onto R n m hmn V.
    exists (a,p); first by rewrite /F /= hP.
    by rewrite /F /= hP.
rewrite -hImage.
exact:(@continuous_suslin_image R Q [the topologicalType of T]
  F [set z:Q|S (F z)] hComplete hSeparable hHausdorff hContinuous hLift).
Qed.

(** Source for [structure_incidence_sets_suslin]: the original
    S1, S2 and S3 measurability premise proved in Federer 3.3.10,
    p. 296, using 3.3.2 and 3.3.3. Their exact kernel lifts are
    original-centre Suslin membership intersected with the actual
    Borel growth loci or actual Suslin accumulation locus. Every
    original incidence set is retained in the continuous image. *)
Theorem structure_incidence_sets_suslin (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->is_suslin_set R A ->
  is_suslin_set R (@structure_first_incidence R n m phi A) /\
  is_suslin_set R (@structure_second_incidence R n m phi A) /\
  is_suslin_set R (@structure_third_incidence R n m A).
Proof.
move=>hPhi hA.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=orthogonal_projection_metric_space R n m.
pose Q:=[the metricType R of metric_product X P].
have hCentres:is_suslin_set R [set z:Q|A z.1].
  exact:(@continuous_preimage_suslin R Q [the topologicalType of X]
    (@fst X P) A (@first_projection_continuous X P) hA).
have hFirst:is_suslin_set R [set z:Q|
    structure_plane_zero_growth m phi A z.1 (structure_projection_kernel hmn z.2)].
  apply:metric_borel_suslin.
  exact:(@structure_projection_zero_growth_borel R n m hmn phi A hPhi).
have hSecond:is_suslin_set R [set z:Q|
    structure_plane_infinite_growth m phi A z.1 (structure_projection_kernel hmn z.2)].
  apply:metric_borel_suslin.
  exact:(@structure_projection_infinite_growth_borel R n m hmn phi A hPhi).
have hThird:=@structure_fibre_accumulation_suslin R n m hmn A hA.
split.
- apply:(@structure_kernel_lift_suslin R n m hmn (@structure_first_incidence R n m phi A)).
  exact:(suslin_binary_intersection hCentres hFirst).
- split.
  + apply:(@structure_kernel_lift_suslin R n m hmn (@structure_second_incidence R n m phi A)).
    exact:(suslin_binary_intersection hCentres hSecond).
  + apply:(@structure_kernel_lift_suslin R n m hmn (@structure_third_incidence R n m A)).
    exact:(suslin_binary_intersection hCentres hThird).
Qed.
