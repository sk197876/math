(** Federer (1969), 3.3.10, p. 296: the complete original
    finite-mass purely unrectifiable Suslin structure theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions EuclideanGrassmannProbability OrthogonalProjectionProbability
  StructureConeUP StructureProjectionKernel StructureGrassmannMeasureFacts
  StructureIncidenceSets StructureIncidenceProductNull StructureFixedProjectionAssertions
  StructureKernelAlmostTransport RectifiableSetUP SuslinSetUP ProductMeasure ProductSections MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_3_10]: COMPLETE Federer 3.3.10, p. 296.
    The ORIGINAL purely (phi,m) unrectifiable Suslin A of finite
    outer mass and ORIGINAL three incidence sets satisfy BOTH
    printed product-nullity identities, ALL THREE assertions for
    EVERY original orthogonal projection, and the final assertion
    for almost every projection under actual theta-star. Original
    A, its fibres, the Grassmann and projection probabilities and
    every natural 0<=m<=n remain. The original phi need only measure
    closed sets. All incidence/product measurability, finite-parent,
    Fubini and probability-transfer premises are proved; no global
    auxiliary object or extra numbered hypothesis is supplied. *)
Theorem federer_3_3_10 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (hStructure:is_structure_measure phi):
  is_purely_measure_m_unrectifiable phi m A ->is_suslin_set R A ->phi A< +oo ->
  let hGamma:=(@structure_grassmann_probability_facts R n (n-m) (leq_subr m n)).1 in
  let nu:=product_measure hStructure.1 hGamma in
  let S1:=@structure_first_incidence R n m phi A in
  let S2:=@structure_second_incidence R n m phi A in
  let S3:=@structure_third_incidence R n m A in
  nu S1=0 /\nu ((A `*` setT) `\` (S2 `|` S3))=0 /\
  (forall p:euclidean_projection_space R n m,
    phi [set a|S1 (a,structure_projection_kernel hmn p)]=0 /\
    euclidean_lebesgue_measure m (euclidean_projection_linear p @`
      [set a|S2 (a,structure_projection_kernel hmn p)])=0 /\
    (euclidean_projection_linear p @` [set a|S3 (a,structure_projection_kernel hmn p)]) `<=`
      [set y|~finite_set (A `&` euclidean_projection_linear p @^-1` [set y])]) /\
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|phi (A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)])=0].
Proof.
move=>hPure hA hFinite; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose S1:=@structure_first_incidence R n m phi A.
pose S2:=@structure_second_incidence R n m phi A.
pose S3:=@structure_third_incidence R n m A.
pose D:=(A `*` setT) `\` (S2 `|` S3).
have [hNull1 [hNullD hAlmostGamma]]:=@structure_incidence_product_null R n m hmn phi A hStructure
  hPure hA hFinite.
split; first exact:hNull1.
split; first exact:hNullD.
split.
- move=>p; split; first exact:(@structure_first_projection_section_null R n m hmn phi A p hStructure hPure).
  split; first exact:(@structure_second_projection_section_null R n m hmn phi A p hStructure hFinite).
  exact:(@structure_third_projection_section_infinite R n m hmn A p).
- have hAlmostTheta:=@structure_kernel_almost_transport R n m hmn _ hAlmostGamma.
  have hProfile p:product_horizontal_section D (structure_projection_kernel hmn p)=
      A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)].
    apply/seteqP; split=>a; rewrite /product_horizontal_section /D /=; tauto.
  have hEqual:[set p:euclidean_projection_space R n m|
      phi (product_horizontal_section D (structure_projection_kernel hmn p))=0]=
      [set p:euclidean_projection_space R n m|
      phi (A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)])=0].
    apply/seteqP; split=>p.
    + change (phi (product_horizontal_section D (structure_projection_kernel hmn p))=0 ->
        phi (A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)])=0).
      by rewrite hProfile.
    + change (phi (A `&` [set a|~(S2 `|` S3) (a,structure_projection_kernel hmn p)])=0 ->
        phi (product_horizontal_section D (structure_projection_kernel hmn p))=0).
      by rewrite hProfile.
  rewrite -hEqual; exact:hAlmostTheta.
Qed.
