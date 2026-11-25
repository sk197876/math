(** Federer (1969), 4.1.23, p. 379:
    complete the finite constant-cell reduction.
    Scalar signs are handled separately, positive
    simple coefficients are normalized and rotated,
    and the attained simple decomposition retains
    exactly the original mass of every coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers ExteriorGrading
  ExteriorPowers AssociatedSubspace ExteriorNorm SimpleElementary SimpleZeroDegree
  OrthogonalMaps OrthogonalFinite OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  CurrentSpaces CurrentCoefficientNorms CurrentZeroDegreeExteriorLaws CurrentDiracDensity
  CurrentCharacteristicDensity CurrentMassSealed CurrentMassFiniteAlgebra CurrentFlatNorm
  SmoothCompactSet PolyhedralCurrentAlgebra CompactCharacteristicCurrent
  CharacteristicCurrentAlgebra CurrentPrefixVectorMass
  CurrentVectorSimpleUnitReduction CurrentVectorOptimalSimpleDecomposition
  MeasurableStandardCellApproximation OrthogonalCellApproximation
  CharacteristicScaledApproximation PolyhedralFiniteApproximationBudget
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section MeasurableCellApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hNX := (inner_norm_real_norm hB).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior (inner_norm hB) x).
Local Notation Current := (fun m => @current_space R h2 n Full hFull m).
Local Notation M := (fun m => @CurrentMass.value R h2 n m Full hFull).
Local Notation VN := (fun m => @current_vector_mass R h2 n m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation cell := (fun m A hA z => @current_characteristic_density R h2 n m
  Leb (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).
Variables K C : smooth_compact_set hNX Full.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior (inner_norm hB) (smooth_compact_carrier C) x.
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Hypothesis hAK : A `<=` smooth_compact_carrier K.
Local Notation spec := (fun m T e P =>
  @polyhedral_current_subspace R h2 n m Full hFull C P /\
  (@current_flat_norm R h2 n m Full hFull C (T-P)<=e%:E)%E /\
  (M m P<=M m T+e%:E)%E).

(** Source for [measurable_zero_cell_polyhedral_approximation]:
    every original scalar coefficient,
    with either sign or zero,
    has the required cell approximation,
    supporting the m=0 reduction
    of Federer 4.1.23, p. 379.
    Orthogonal maps are not used
    to reverse the scalar unit. *)
Theorem measurable_zero_cell_polyhedral_approximation
    (z : exterior_power X 0%N) epsilon (hEpsilon : 0<epsilon) :
  exists P : Current 0%N, spec 0%N (cell 0%N A hA z) epsilon P.
Proof.
pose unit := @current_scalar_multivector_unit R n.
have hBase delta (hDelta : 0<delta) :
    exists P : Current 0%N, spec 0%N (cell 0%N A hA unit) delta P.
  have h := @measurable_standard_cell_polyhedral_approximation R h2 n 0%N
    (leq0n n) K C hKC A hA hAK delta hDelta.
  by rewrite current_empty_frame_scalar_unit in h.
pose c := exterior_zeroth_inverse X z.
have hValue : z=c*:unit.
  rewrite /unit /current_scalar_multivector_unit -linearZ.
  change (z=exterior_zeroth_inclusion X (c*1)).
  by rewrite mulr1 exterior_zeroth_inverseK.
have h := @characteristic_scaled_polyhedral_approximation R h2 n 0%N K C
  A hA hAK unit hBase c epsilon hEpsilon.
by rewrite -hValue in h.
Qed.

(** Source for [measurable_simple_cell_polyhedral_approximation]:
    each original positive-degree simple
    coefficient is normalized, rotated and
    scaled back with its exact
    mass cost, supporting Federer
    4.1.23, p. 379.
    Zero coefficients are handled before
    choosing a unit direction or rotation. *)
Theorem measurable_simple_cell_polyhedral_approximation j (hMN : (j.+1<=n)%N)
    (z : exterior_power X j.+1) (hSimple : simple z)
    epsilon (hEpsilon : 0<epsilon) :
  exists P : Current j.+1, spec j.+1 (cell j.+1 A hA z) epsilon P.
Proof.
case: (eqVneq z 0)=> [->|hNonzero].
- exists 0; split; first exact: subspace_zero.
  rewrite characteristic_current_coefficient_zero subrr current_flat_norm_zero
    current_mass_zero add0e.
  split; rewrite lee_fin; exact: ltW hEpsilon.
- have [a [u [hPositive [hUSimple [hUnit [hValue hMass]]]]]] :=
    @current_positive_simple_unit_factor R h2 n j z hSimple hNonzero.
  have [o hCoordinate] := @current_simple_unit_coordinate_rotation R h2 n j.+1
    (ltn0Sn j) hMN u hUSimple hUnit.
  pose f := hom_as_linear (@orthogonal_element_map R X B hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) o).
  have hF : is_orthogonal_map B B f := @orthogonal_element_orthogonal R X B hB
    n (@coordinate_basis R n) (@coordinate_basisP R n) o.
  have [g [hFG [hGF hG]]] := @orthogonal_endomorphism_inverse_exists R X B hB
    n (@coordinate_basis R n) (@coordinate_basisP R n) f hF.
  have hBase delta (hDelta : 0<delta) :
      exists P : Current j.+1, spec j.+1 (cell j.+1 A hA u) delta P.
    exact: (@orthogonal_cell_polyhedral_approximation R h2 n j.+1 hMN f g hF hG
      hFG hGF u hCoordinate K C hKC A hA hAK delta hDelta).
  have h := @characteristic_scaled_polyhedral_approximation R h2 n j.+1 K C
    A hA hAK u hBase a epsilon hEpsilon.
  by rewrite -hValue in h.
Qed.

(** Source for [measurable_cell_polyhedral_approximation]:
    the full constant-cell reduction
    of Federer 4.1.23, p. 379,
    retains the exact attained simple
    mass decomposition before combining the
    individual approximants. No coordinatewise
    inflation of the printed mass is used. *)
Theorem measurable_cell_polyhedral_approximation m (hMN : (m<=n)%N)
    (z : exterior_power X m) epsilon (hEpsilon : 0<epsilon) :
  exists P : Current m, spec m (cell m A hA z) epsilon P.
Proof.
case: m hMN z=> [|j] hMN z.
- exact: measurable_zero_cell_polyhedral_approximation.
- have [k [u [_ [hSimple [hSum [hCost _]]]]]] :=
    @current_vector_optimal_simple_decomposition R h2 n j z.
  have hAFinite : (Leb A< +oo)%E := le_lt_trans
    (measure_mono (euclidean_lebesgue_is_measure R n) hAK)
    (@euclidean_distribution_measure_compact_finite R n (smooth_compact_carrier K)
      (smooth_compact_is_compact K)).
  have hANumber : Leb A \is a fin_num.
    by rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R n) A)).
  pose cost := fun i : 'I_k => VN j.+1 (u i)*fine (Leb A).
  have hMassCell v : M j.+1 (cell j.+1 A hA v)=(VN j.+1 v*fine (Leb A))%:E.
    by rewrite (@compact_characteristic_current_properties R h2 n j.+1 A hA v K hAK).1
      -(fineK hANumber) -EFinM.
  have hPieces i delta (hDelta : 0<delta) : exists P : Current j.+1,
      @polyhedral_current_subspace R h2 n j.+1 Full hFull C P /\
      (@current_flat_norm R h2 n j.+1 Full hFull C (cell j.+1 A hA (u i)-P)<=delta%:E)%E /\
      (M j.+1 P<=(cost i+delta)%:E)%E.
    have [P [hPoly [hError hMass]]] := @measurable_simple_cell_polyhedral_approximation
      j hMN (u i) (hSimple i) delta hDelta.
    exists P; split; first exact: hPoly.
    split; first exact: hError.
    by rewrite hMassCell -EFinD in hMass.
  have [P [hPoly [hError hMass]]] := @polyhedral_finite_approximation_budget R h2 n j.+1
    Full hFull C [the finType of 'I_k] (fun i => cell j.+1 A hA (u i)) cost
    hPieces epsilon hEpsilon.
  have hCurrent : cell j.+1 A hA z=\sum_i cell j.+1 A hA (u i).
    by rewrite hSum characteristic_current_coefficient_finite_sum.
  have hTotalCost : \sum_i cost i=VN j.+1 z*fine (Leb A).
    by rewrite /cost -mulr_suml -hCost.
  exists P; split; first exact: hPoly.
  split; first by rewrite hCurrent.
  by rewrite hTotalCost EFinD -hMassCell in hMass.
Qed.
End MeasurableCellApproximation.
