(** Federer (1969), 4.1.23, p. 380:
    identify the original scalar rectangle product
    with the literal constant-coordinate-vector current
    on its compact Cartesian box. The coefficient
    is the same first-coordinate m-vector used
    by the preceding simple-unit rotation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers ExteriorGrading
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentCharacteristicDensity
  CurrentDegreeTransport CurrentCartesianDomain CurrentCartesianCompact
  CurrentAmbientCartesianProduct CurrentCoefficientNorms
  CurrentCartesianPrefixVector CurrentCharacteristicDegreeTransport
  CharacteristicCartesianCurrent OrientedRectangleDomain ScalarSegmentFactors
  CurrentScalarRectangle ScalarRectangleBoxDensity ClosedCoordinateBoxConvex
  ClosedCoordinateBoxGeometry SmoothCompactSet TopologicalBorel
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext.
From Federer Require Import CurrentDiracDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectangleProductDensity.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable f : seq (R*R).
Hypothesis hOrdered : @scalar_rectangle_ordered R f.
Local Notation m := (oriented_rectangle_dimension (@scalar_segment_factors R f)).
Variable n : nat.
Local Notation Full := (fun d : nat => fun _ : R_n R d => True).
Local Notation hFull := (fun (d : nat) (x : R_n R d) (_ : True) =>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation lower := ([ffun i : 'I_m => (nth (0,0) f (val i)).1] : R_n R m).
Local Notation upper := ([ffun i : 'I_m => (nth (0,0) f (val i)).2] : R_n R m).
Local Notation D := (@closed_coordinate_box_index R m lower upper).
Variable B : smooth_compact_set hNY (Full n).
Local Notation Box := (@euclidean_cartesian_set R m n (smooth_compact_carrier D)
  (smooth_compact_carrier B)).
Local Notation hBox := (@current_cartesian_compact R m n (smooth_compact_carrier D)
  (smooth_compact_carrier B) (smooth_compact_is_compact D) (smooth_compact_is_compact B)).
Local Notation hDM := (@euclidean_distribution_measure_borel R m (smooth_compact_carrier D)
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
    (smooth_compact_is_compact D)))).
Local Notation hBM := (@euclidean_distribution_measure_borel R n (smooth_compact_carrier B)
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNY))
    (smooth_compact_is_compact B)))).
Local Notation hBoxM := (@euclidean_distribution_measure_borel R (m+n) Box
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNZ)) hBox))).
Local Notation Leb := (fun d => @euclidean_lebesgue_measure R d).
Local Notation cell := (fun d k A hA z => @current_characteristic_density R h2 d k
  (Leb d) (euclidean_lebesgue_is_measure R d) (@euclidean_distribution_measure_borel R d)
  (@euclidean_distribution_measure_compact_finite R d) A hA z).
Local Notation top := (e_lambda (@coordinate_basis R m) (ord_tuple m)).
Local Notation unit := (@current_scalar_multivector_unit R n).
Local Notation prefix := (e_lambda (fun i : 'I_m =>
  @coordinate_basis R (m+n) (widen_ord (leq_addr n m) i)) (ord_tuple m)).
Local Notation S := (cell n 0%N (smooth_compact_carrier B) hBM unit).
Local Notation Rectangle := (@current_scalar_rectangle R h2 f).
Local Notation Tr := (@current_degree_transport R h2 (m+n) (Full (m+n)) (hFull (m+n))
  (m+0) m (addn0 m)).

(** Source for [scalar_rectangle_product_characteristic_density]:
    R times S is precisely the
    original Lebesgue current on D times B
    with coefficient e_1 wedge ... wedge e_m,
    Federer 4.1.23, p. 380.
    The transverse compact may be empty,
    null or zero-dimensional, and m=0
    retains the original scalar unit. *)
Theorem scalar_rectangle_product_characteristic_density :
  Tr (@current_ambient_cartesian_product R h2 m n m 0%N Rectangle S)=
    cell (m+n) m Box hBoxM prefix.
Proof.
have hRectangle := (@scalar_rectangle_box_density_properties R h2 f hOrdered).1.
have hProduct := @characteristic_cartesian_current R h2 m n m 0%N
  (smooth_compact_carrier D) (smooth_compact_carrier B) hDM hBM hBoxM top unit.
rewrite hRectangle hProduct current_characteristic_degree_transport
  current_cartesian_top_zero_standard_vector.
reflexivity.
Qed.
End RectangleProductDensity.
