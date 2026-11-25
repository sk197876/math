(** Federer (1969), 4.1.23, p. 380:
    the completed rectangle-times-transverse-current
    construction approximates the literal coordinate-vector
    density on the same compact box, with
    equal mass and any prescribed flat error. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm InnerConvex HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers ExteriorGrading
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentCharacteristicDensity
  CurrentCoefficientNorms CurrentMassSealed CurrentFlatNorm CurrentDegreeTransport
  CurrentCartesianDomain CurrentCartesianCompact CurrentAmbientCartesianProduct
  OrientedRectangleDomain ScalarSegmentFactors CurrentScalarRectangle
  ScalarRectangleProductDensity ScalarRectangleProductApproximation
  ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry SmoothCompactSet
  TopologicalBorel PolyhedralCurrentAlgebra EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectangleCoordinateApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable f : seq (R*R).
Hypothesis hOrdered : @scalar_rectangle_ordered R f.
Local Notation m := (oriented_rectangle_dimension (@scalar_segment_factors R f)).
Variable n : nat.
Local Notation Full := (fun d : nat => fun _ : R_n R d => True).
Local Notation hFull := (fun (d : nat) (x : R_n R d) (_ : True) =>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation lower := ([ffun i : 'I_m => (nth (0,0) f (val i)).1] : R_n R m).
Local Notation upper := ([ffun i : 'I_m => (nth (0,0) f (val i)).2] : R_n R m).
Local Notation D := (@closed_coordinate_box_index R m lower upper).
Variable B : smooth_compact_set hNY (Full n).
Hypothesis hBConvex : is_inner_convex (smooth_compact_carrier B).
Local Notation Box := (@euclidean_cartesian_set R m n (smooth_compact_carrier D)
  (smooth_compact_carrier B)).
Local Notation hBox := (@current_cartesian_compact R m n (smooth_compact_carrier D)
  (smooth_compact_carrier B) (smooth_compact_is_compact D) (smooth_compact_is_compact B)).
Local Notation K := (@Build_smooth_compact_set R (R_n R (m+n))
  (inner_norm (@euclidean_inner_productP R (m+n))) hNZ (Full (m+n)) Box
  (fun _ _ => Logic.I) hBox).
Local Notation hBoxM := (@euclidean_distribution_measure_borel R (m+n) Box
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNZ)) hBox))).
Local Notation prefix := (e_lambda (fun i : 'I_m => @coordinate_basis R (m+n)
  (widen_ord (leq_addr n m) i)) (ord_tuple m)).
Local Notation T := (@current_characteristic_density R h2 (m+n) m
  (@euclidean_lebesgue_measure R (m+n)) (euclidean_lebesgue_is_measure R (m+n))
  (@euclidean_distribution_measure_borel R (m+n))
  (@euclidean_distribution_measure_compact_finite R (m+n)) Box hBoxM prefix).
Local Notation Current := (@current_space R h2 (m+n) (Full (m+n)) (hFull (m+n)) m).
Local Notation M := (@CurrentMass.value R h2 (m+n) m (Full (m+n)) (hFull (m+n))).

(** Source for [scalar_rectangle_coordinate_polyhedral_approximation]:
    the literal coordinate-vector current on
    D times B has a real
    polyhedral approximant in the same
    compact box, flat error at
    most epsilon and exactly its
    mass, Federer 4.1.23, p. 380. *)
Theorem scalar_rectangle_coordinate_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current,
    @polyhedral_current_subspace R h2 (m+n) m (Full (m+n)) (hFull (m+n)) K P /\
    (@current_flat_norm R h2 (m+n)%N m (Full (m+n)%N) (hFull (m+n)%N) K (T-P)<=epsilon%:E)%E /\
    M P=M T.
Proof.
have h := @scalar_rectangle_product_polyhedral_approximation R h2 f hOrdered
  n B hBConvex epsilon hEpsilon.
rewrite (@scalar_rectangle_product_characteristic_density R h2 f hOrdered n B) in h.
exact: h.
Qed.
End RectangleCoordinateApproximation.
