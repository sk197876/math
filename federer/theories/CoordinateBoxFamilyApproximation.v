(** Federer (1969), 4.1.23, pp. 379–380:
    assemble the constructed coordinate-box approximants
    in the original, possibly nonconvex compact C.
    Every generator is admitted through its whole
    box closure, rather than only the support
    of a cancelling finite sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct InnerMetric FiniteCoordinates FiniteExteriorPowers
  ExteriorGrading CurrentSpaces CurrentCoefficientNorms CurrentMassSealed
  CurrentFlatNorm CurrentFlatCompactMonotone SmoothCompactSet TopologicalBorel
  PolyhedralCurrentAlgebra PolyhedralFiniteApproximationBudget
  CurrentPrefixVectorMass CoordinateBoxStandardApproximation
  ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry
  CharacteristicCurrentNullBoundary CharacteristicCurrentFiniteUnion
  CompactCharacteristicCurrent CurrentCharacteristicDensity
  EuclideanOpenCoordinateBoxUP EuclideanOpenCoordinateBoxMeasure
  EuclideanOpenBoxMeasurability FiniteDisjointOpenBoxFamilyUP FiniteDisjointOpenBoxVolume
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanDistributionMeasureContext
  MeasureUP.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section BoxFamilyApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Hypothesis hMN : (m<=n)%N.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation xi := (e_lambda (fun i : 'I_m => @coordinate_basis R n
  (widen_ord hMN i)) (ord_tuple m)).
Local Notation cell := (fun A hA => @current_characteristic_density R h2 n m Leb
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA xi).
Variable C : smooth_compact_set hNX Full.
Variable I : finType.
Variables a b : I -> X.
Variable G : I -> set X.
Hypothesis hFamily : is_finite_disjoint_open_box_family a b G.
Hypothesis hBoxes : forall i, @closed_coordinate_box R n (a i) (b i) `<=`
  smooth_compact_carrier C.
Local Notation H := (\bigcup_i G i).
Local Notation hHM := (@finite_disjoint_open_box_union_measurable R n I a b G hFamily).

(** Source for [coordinate_box_family_polyhedral_approximation]:
    the original disjoint rectangular union
    with its standard coordinate coefficient
    has a real polyhedral approximation
    in C with any prescribed flat
    error and mass at most its
    Lebesgue volume plus that error,
    supporting Federer 4.1.23, p. 379. *)
Theorem coordinate_box_family_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current, @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (@current_flat_norm R h2 n m Full hFull C (cell H hHM-P)<=epsilon%:E)%E /\
    (M P<=Leb H+epsilon%:E)%E.
Proof.
pose hGM := fun i => @open_coordinate_box_measurable R n (a i) (b i) (G i)
  (finite_disjoint_open_box_law hFamily i).
pose cost := fun i => \prod_(j : 'I_n) (b i j-a i j).
have hPieces i delta (hDelta : 0<delta) : exists P : Current,
    @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (@current_flat_norm R h2 n m Full hFull C (cell (G i) (hGM i)-P)<=delta%:E)%E /\
    (M P<=(cost i+delta)%:E)%E.
  pose B := @closed_coordinate_box_index R n (a i) (b i).
  pose hBM := @euclidean_distribution_measure_borel R n (smooth_compact_carrier B)
    (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
      (smooth_compact_is_compact B))).
  have hProper := finite_disjoint_open_box_law hFamily i.
  have hClosed := @proper_coordinate_box_current_closure R h2 n m (a i) (b i)
    (G i) hProper xi.
  have [P [hPoly [hError hMass]]] := @coordinate_box_prefix_polyhedral_approximation
    R h2 n m hMN (a i) (b i) hProper.1 hBM delta hDelta.
  have hCellMass := (@compact_characteristic_current_properties R h2 n m
    (smooth_compact_carrier B) hBM xi B (fun _ hx => hx)).1.
  rewrite (@current_prefix_vector_mass_one R h2 n m hMN) mul1e
    (@euclidean_closed_box R n (a i) (b i) (fun j => ltW (hProper.1 j))) in hCellMass.
  exists P; split.
  - exact: (@polyhedral_current_monotone R h2 n m Full hFull B C (@hBoxes i) P hPoly).
  split.
  - have hMeasProof : hGM i = @open_coordinate_box_measurable R n
        (a i) (b i) (G i) hProper := Prop_irrelevance _ _.
    rewrite hMeasProof hClosed; exact: (le_trans
      (@current_flat_compact_monotone R h2 n m Full hFull B C (@hBoxes i) _)
      hError).
  - rewrite hMass hCellMass lee_fin; by rewrite lerDl; exact: ltW hDelta.
have [P [hPoly [hError hMass]]] := @polyhedral_finite_approximation_budget R h2 n m
  Full hFull C I (fun i => cell (G i) (hGM i)) cost hPieces epsilon hEpsilon.
have hUnion := @characteristic_current_disjoint_finite_union R h2 n m I G hGM hHM
  (@finite_disjoint_open_box_disjoint_law R n I a b G hFamily) xi.
exists P; split; first exact: hPoly.
split; first by rewrite hUnion.
rewrite (@finite_disjoint_open_box_union_volume R n I a b G hFamily) -EFinD.
exact: hMass.
Qed.
End BoxFamilyApproximation.
