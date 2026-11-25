(** Federer (1969), 4.1.23, p. 379:
    approximate any measurable cell with the
    standard unit m-vector by the original
    rectangular construction. The two-sided set error
    controls flat error, while the separate volume
    allowance preserves the printed mass budget. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormBoundedLinearTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers
  ExteriorGrading CurrentSpaces CurrentSupportGeometry CurrentCoefficientNorms
  CurrentMassSealed CurrentFlatNorm CurrentFlatMassComparison CurrentFlatFiniteArithmetic
  CurrentCharacteristicDensity SmoothCompactSet PolyhedralCurrentAlgebra
  CompactCharacteristicCurrent CharacteristicCurrentDifferenceMass
  CurrentPrefixVectorMass EuclideanCellBoxApproximation CoordinateBoxFamilyApproximation
  ClosedCoordinateBoxConvex EuclideanOpenCoordinateBoxUP FiniteDisjointOpenBoxFamilyUP
  FiniteDisjointOpenBoxVolume EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  MeasureUP.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section StandardCellApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Hypothesis hMN : (m<=n)%N.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation xi := (e_lambda (fun i : 'I_m => @coordinate_basis R n
  (widen_ord hMN i)) (ord_tuple m)).
Local Notation cell := (fun A hA => @current_characteristic_density R h2 n m Leb
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA xi).
Variables K C : smooth_compact_set hNX Full.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NX (smooth_compact_carrier C) x.
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Hypothesis hAK : A `<=` smooth_compact_carrier K.
Local Notation T := (cell A hA).
Local Notation F := (@current_flat_norm R h2 n m Full hFull C).

(** Source for [measurable_standard_cell_polyhedral_approximation]:
    the measurable unit-coordinate-cell reduction
    in Federer 4.1.23, p. 379,
    with its original containing compacts
    and both printed approximation bounds.
    The cell is merely measurable;
    C need not be convex. *)
Theorem measurable_standard_cell_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current, @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (F (T-P)<=epsilon%:E)%E /\ (M P<=M T+epsilon%:E)%E.
Proof.
pose delta := epsilon/3.
have hThree : 0<(3:R) by rewrite ltr0n.
have hDelta : 0<delta := divr_gt0 hEpsilon hThree.
have hBudget : delta+delta<=epsilon by rewrite /delta; lra.
pose W := @interior XT (smooth_compact_carrier C).
have hKW : smooth_compact_carrier K `<=` W.
  move=> x hx; exact: (norm_domain_interior_neighbourhood hNX _ _).1 (@hKC x hx).
have hWOpen : @open XT W := open_interior _.
have [I [a [b [G [hFamily [hBoxes [hSetError hVolume]]]]]]] :=
  @euclidean_cell_box_approximation R n A (smooth_compact_carrier K) W delta hA
    (smooth_compact_is_compact K) hAK hWOpen hKW hDelta.
pose H := \bigcup_i G i.
pose hHM := @finite_disjoint_open_box_union_measurable R n I a b G hFamily.
have hBoxesC i : @closed_coordinate_box R n (a i) (b i) `<=` smooth_compact_carrier C.
  exact: subset_trans (hBoxes i) (@interior_subset XT (smooth_compact_carrier C)).
have hHC : H `<=` smooth_compact_carrier C.
  move=> x [i _ hx]; apply: (@hBoxesC i x).
  move=> j; have /andP [hLow hHigh] :=
    ((finite_disjoint_open_box_law hFamily i).2 x).1 hx j.
  apply/andP; split; exact: ltW.
have hAC : A `<=` smooth_compact_carrier C.
  exact: subset_trans hAK (subset_trans hKW (@interior_subset XT (smooth_compact_carrier C))).
have hSupportA := (@compact_characteristic_current_properties R h2 n m A hA xi C hAC).2.
have hSupportH := (@compact_characteristic_current_properties R h2 n m H hHM xi C hHC).2.
have hSupportDifference : @current_support R h2 n Full hFull m (T-cell H hHM)
    `<=` smooth_compact_carrier C.
  have h := @current_support_linear_subset R h2 n m Full hFull C
    (-1) (cell H hHM) T hSupportH hSupportA.
  by rewrite scaleN1r addrC in h.
have hDifferenceMass := @characteristic_current_difference_mass R h2 n m
  A H hA hHM xi C hAC hHC.
rewrite (@current_prefix_vector_mass_one R h2 n m hMN) mul1e in hDifferenceMass.
have hFirst : (F (T-cell H hHM)<delta%:E)%E.
  apply: (le_lt_trans (@current_flat_norm_le_mass R h2 n m Full hFull C
    (T-cell H hHM) hSupportDifference)).
  by rewrite hDifferenceMass.
have [P [hPoly [hError hMass]]] := @coordinate_box_family_polyhedral_approximation R h2 n m
  hMN C I a b G hFamily hBoxesC delta hDelta.
have hFiniteFirst : (F (T-cell H hHM)< +oo)%E := lt_trans hFirst (ltry delta).
have hFiniteSecond : (F (cell H hHM-P)< +oo)%E := le_lt_trans hError (ltry delta).
have hTriangle := @current_flat_finite_triangle R h2 n m Full hFull C
  (T-cell H hHM) (cell H hHM-P) hFiniteFirst hFiniteSecond.
have hDifference : (T-cell H hHM)+(cell H hHM-P)=T-P by rewrite addrA subrK.
rewrite hDifference in hTriangle.
have hSum := leeD (ltW hFirst) hError.
rewrite -EFinD in hSum.
have hMassA := (@compact_characteristic_current_properties R h2 n m A hA xi K hAK).1.
rewrite (@current_prefix_vector_mass_one R h2 n m hMN) mul1e in hMassA.
exists P; split; first exact: hPoly.
split.
- apply: (le_trans (le_trans hTriangle hSum)); by rewrite lee_fin.
- have hVolumeEnlarge := leeD hVolume (lexx delta%:E).
  apply: (le_trans (le_trans hMass hVolumeEnlarge)).
  rewrite hMassA -addeA -EFinD.
  apply: leeD; first exact: lexx.
  by rewrite lee_fin.
Qed.
End StandardCellApproximation.
