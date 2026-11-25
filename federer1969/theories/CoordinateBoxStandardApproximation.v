(** Federer (1969), 4.1.23, pp. 379–380:
    every proper closed coordinate box with the
    standard first-coordinate m-vector has an equal-mass
    real polyhedral approximation in that same box.
    Choose the original scalar rectangle from its
    first endpoints and use the actual product construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers ExteriorGrading
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentCharacteristicDensity
  CurrentMassSealed CurrentFlatNorm SmoothCompactSet SmoothCompactSetExtensionality
  TopologicalBorel CurrentCartesianCompact PolyhedralCurrentAlgebra
  ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry CoordinateBoxCartesianFactors
  OrientedRectangleDomain ScalarSegmentFactors ScalarRectangleEndpointSequence
  ScalarRectangleCoordinateApproximation CharacteristicCurrentAlgebra
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext.
From Federer Require Import MeasureUP.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_box_standard_polyhedral_approximation]:
    the last special case in
    Federer 4.1.23, pp. 379–380:
    A is the original closed box,
    xi=e_1 wedge ... wedge e_m,
    F_A(T-P)<=epsilon and M(P)=M(T).
    The two blocks may have dimension zero;
    all entire simplex hulls stay in A. *)
Theorem coordinate_box_standard_polyhedral_approximation (R : realType)
    (h2 : (1+1:R)!=0) m n (a b : R_n R (m+n))
    (hStrict : forall i, a i<b i)
    (hAM : measure_measurable (@euclidean_lebesgue_measure R (m+n))
      (@closed_coordinate_box R (m+n) a b))
    (epsilon : R) (hEpsilon : 0<epsilon) :
  let Full := fun _ : R_n R (m+n) => True in
  let hFull := fun (x : R_n R (m+n)) (_ : True) => norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R (m+n))) x in
  let A := @closed_coordinate_box R (m+n) a b in
  let K := @closed_coordinate_box_index R (m+n) a b in
  let xi := e_lambda (fun i : 'I_m => @coordinate_basis R (m+n)
    (widen_ord (leq_addr n m) i)) (ord_tuple m) in
  let T := @current_characteristic_density R h2 (m+n) m
    (@euclidean_lebesgue_measure R (m+n)) (euclidean_lebesgue_is_measure R (m+n))
    (@euclidean_distribution_measure_borel R (m+n))
    (@euclidean_distribution_measure_compact_finite R (m+n)) A hAM xi in
  exists P : @current_space R h2 (m+n) Full hFull m,
    @polyhedral_current_subspace R h2 (m+n) m Full hFull K P /\
    (@current_flat_norm R h2 (m+n)%N m Full hFull K (T-P)<=epsilon%:E)%E /\
    @CurrentMass.value R h2 (m+n) m Full hFull P=
      @CurrentMass.value R h2 (m+n) m Full hFull T.
Proof.
pose f := @scalar_rectangle_endpoint_sequence R m
  (euclidean_block_split a).1 (euclidean_block_split b).1.
have hDimension : oriented_rectangle_dimension (@scalar_segment_factors R f)=m.
  exact: scalar_rectangle_endpoint_sequence_dimension.
have hEntries (i : 'I_m) : nth (0,0) f (val i)=
    (a (lshift n i),b (lshift n i)).
  by rewrite /f scalar_rectangle_endpoint_sequence_values /euclidean_block_split !ffunE.
have hOrdered : @scalar_rectangle_ordered R f.
  apply: scalar_rectangle_endpoint_sequence_ordered=> i.
  rewrite /euclidean_block_split !ffunE; exact: hStrict (lshift n i).
clearbody f.
cbn zeta; case: m /hDimension in a b hStrict hAM hEntries *.
pose d := oriented_rectangle_dimension (@scalar_segment_factors R f).
pose Full := fun _ : R_n R (d+n) => True.
pose hFull := fun (x : R_n R (d+n)) (_ : True) =>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R (d+n))) x.
pose A := @closed_coordinate_box R (d+n) a b.
pose K := @closed_coordinate_box_index R (d+n) a b.
pose xi := e_lambda (fun i : 'I_d => @coordinate_basis R (d+n)
  (widen_ord (leq_addr n d) i)) (ord_tuple d).
pose T := @current_characteristic_density R h2 (d+n) d
  (@euclidean_lebesgue_measure R (d+n)) (euclidean_lebesgue_is_measure R (d+n))
  (@euclidean_distribution_measure_borel R (d+n))
  (@euclidean_distribution_measure_compact_finite R (d+n)) A hAM xi.
pose low : R_n R d := [ffun i => (nth (0,0) f (val i)).1].
pose high : R_n R d := [ffun i => (nth (0,0) f (val i)).2].
pose D := @closed_coordinate_box_index R d low high.
pose B := @closed_coordinate_box_index R n (euclidean_block_split a).2 (euclidean_block_split b).2.
pose Box := @euclidean_cartesian_set R d n (smooth_compact_carrier D)
  (smooth_compact_carrier B).
pose hBox := @current_cartesian_compact R d n (smooth_compact_carrier D)
  (smooth_compact_carrier B) (smooth_compact_is_compact D) (smooth_compact_is_compact B).
pose hNZ := inner_norm_real_norm (@euclidean_inner_productP R (d+n)).
pose K0 := @Build_smooth_compact_set R (R_n R (d+n))
  (inner_norm (@euclidean_inner_productP R (d+n))) hNZ Full Box
  (fun _ _ => Logic.I) hBox.
pose hBoxM := @euclidean_distribution_measure_borel R (d+n) Box
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNZ)) hBox)).
pose T0 := @current_characteristic_density R h2 (d+n) d
  (@euclidean_lebesgue_measure R (d+n)) (euclidean_lebesgue_is_measure R (d+n))
  (@euclidean_distribution_measure_borel R (d+n))
  (@euclidean_distribution_measure_compact_finite R (d+n)) Box hBoxM xi.
have hLow : low=(euclidean_block_split a).1.
  apply/ffunP=> i; rewrite /low /euclidean_block_split !ffunE.
  by rewrite (hEntries i).
have hHigh : high=(euclidean_block_split b).1.
  apply/ffunP=> i; by rewrite /high /euclidean_block_split !ffunE (hEntries i).
have hBoxSet : Box=A.
  rewrite /Box /D /B /= hLow hHigh /A.
  exact: esym (closed_coordinate_box_cartesian_factors a b).
have hIndex : K0=K.
  exact: (@smooth_compact_set_extensionality R (R_n R (d+n))
    (inner_norm (@euclidean_inner_productP R (d+n))) hNZ Full K0 K hBoxSet).
have hCurrent : T0=T.
  exact: (@characteristic_current_set_congruence R h2 (d+n) d
    Box A hBoxM hAM xi hBoxSet).
have hApprox := @scalar_rectangle_coordinate_polyhedral_approximation R h2 f hOrdered n B
  (@closed_coordinate_box_convex R n (euclidean_block_split a).2 (euclidean_block_split b).2)
  epsilon hEpsilon.
change (exists P : @current_space R h2 (d+n) Full hFull d,
  @polyhedral_current_subspace R h2 (d+n) d Full hFull K0 P /\
  (@current_flat_norm R h2 (d+n)%N d Full hFull K0 (T0-P)<=epsilon%:E)%E /\
  @CurrentMass.value R h2 (d+n) d Full hFull P=
    @CurrentMass.value R h2 (d+n) d Full hFull T0) in hApprox.
by rewrite hIndex hCurrent in hApprox.
Qed.

(** Source for [coordinate_box_prefix_polyhedral_approximation]:
    the same original box construction
    is stated in its original
    ambient R^N for every m<=N,
    supporting Federer 4.1.23,
    pp. 379–380. Only the
    equality N=m+(N-m) is eliminated;
    no embedding into a different
    ambient space is imposed. *)
Theorem coordinate_box_prefix_polyhedral_approximation (R : realType)
    (h2 : (1+1:R)!=0) N m (hMN : (m<=N)%N) (a b : R_n R N)
    (hStrict : forall i, a i<b i)
    (hAM : measure_measurable (@euclidean_lebesgue_measure R N)
      (@closed_coordinate_box R N a b))
    (epsilon : R) (hEpsilon : 0<epsilon) :
  let Full := fun _ : R_n R N => True in
  let hFull := fun (x : R_n R N) (_ : True) => norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R N)) x in
  let A := @closed_coordinate_box R N a b in
  let K := @closed_coordinate_box_index R N a b in
  let xi := e_lambda (fun i : 'I_m => @coordinate_basis R N
    (widen_ord hMN i)) (ord_tuple m) in
  let T := @current_characteristic_density R h2 N m
    (@euclidean_lebesgue_measure R N) (euclidean_lebesgue_is_measure R N)
    (@euclidean_distribution_measure_borel R N)
    (@euclidean_distribution_measure_compact_finite R N) A hAM xi in
  exists P : @current_space R h2 N Full hFull m,
    @polyhedral_current_subspace R h2 N m Full hFull K P /\
    (@current_flat_norm R h2 N m Full hFull K (T-P)<=epsilon%:E)%E /\
    @CurrentMass.value R h2 N m Full hFull P=
      @CurrentMass.value R h2 N m Full hFull T.
Proof.
have [k hDimension] : exists k, N=(m+k)%N.
  exists (N-m)%N; symmetry; exact: subnKC hMN.
subst N.
have hProof : hMN=leq_addr k m := Prop_irrelevance _ _.
subst hMN.
exact: (@coordinate_box_standard_polyhedral_approximation R h2 m k
  a b hStrict hAM epsilon hEpsilon).
Qed.
