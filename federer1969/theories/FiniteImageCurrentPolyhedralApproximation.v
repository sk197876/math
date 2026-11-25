(** Federer (1969), 4.1.23, p. 379:
    combine all measurable cells of the original
    finite-image L1 coefficient. Their exact original
    sizes sum to its actual mass, so
    the cell approximations retain the sharp
    mass allowance and the original compact C. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentSpaces CurrentCoefficientNorms CurrentMassSealed CurrentFlatNorm
  CurrentDensityAction CurrentDensityArithmetic CurrentDensityUniqueness CurrentCharacteristicDensity
  CompactSummableFieldSealed CompactSummableFieldLaws CompactSummableFiniteCells
  CharacteristicCurrentDifferenceMass CompactCharacteristicCurrent
  MeasurableCellPolyhedralApproximation PolyhedralFiniteApproximationBudget
  SmoothCompactSet TopologicalBorel PolyhedralCurrentAlgebra
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext MeasureUP
  CharacteristicFunctionUP CharacteristicFunctionSealed.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section FiniteImagePolyhedralApproximation.
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
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation W := (@CompactSummableField.space R XT V VN hVN Leb hLeb).
Local Notation value := (@compact_summable_field_value R XT V VN hVN Leb hLeb).
Local Notation size := (@compact_summable_field_size R XT V VN hVN Leb hLeb).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation cell := (fun A hA z => @current_characteristic_density R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).
Variables K C : smooth_compact_set hNX Full.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NX (smooth_compact_carrier C) x.
Variable f : W.
Hypothesis hFinite : finite_set (value f @` setT).
Hypothesis hOff : forall x, ~smooth_compact_carrier K x -> value f x=0.
Variable T : Current.
Hypothesis hT : @is_current_density_action R h2 n m Leb (value f) T.

(** Source for [finite_image_current_polyhedral_approximation]:
    the original finite-image coefficient
    reduction in Federer 4.1.23,
    p. 379, is now assembled
    from its actual measurable cells
    and their exact mass costs.
    No smoothness, normality or representation
    hypothesis is imposed on the cells. *)
Theorem finite_image_current_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current, @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (@current_flat_norm R h2 n m Full hFull C (T-P)<=epsilon%:E)%E /\
    (M P<=M T+epsilon%:E)%E.
Proof.
have hKMeas := @euclidean_distribution_measure_borel R n (smooth_compact_carrier K)
  (closed_borel_set (compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K))).
have hKFinite := @euclidean_distribution_measure_compact_finite R n
  (smooth_compact_carrier K) (smooth_compact_is_compact K).
have [I [v [A [w [hCells [_ [_ [hValues [hCosts [hSum hTotal]]]]]]]]]] :=
  @compact_summable_finite_cell_decomposition R XT V VN hVN Leb hLeb f
    (smooth_compact_carrier K) (smooth_compact_is_compact K) hKMeas hKFinite hFinite hOff.
pose S := fun i => cell (A i) (hCells i).1 (v i).
have hMassCell i : M (S i)=(size (w i))%:E.
  rewrite (@compact_characteristic_current_properties R h2 n m (A i)
    (hCells i).1 (v i) K (hCells i).2.2).1.
  exact: esym (hCosts i).
have hPieces i delta (hDelta : 0<delta) : exists P : Current,
    @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (@current_flat_norm R h2 n m Full hFull C (S i-P)<=delta%:E)%E /\
    (M P<=(size (w i)+delta)%:E)%E.
  have [P [hPoly [hError hMass]]] := @measurable_cell_polyhedral_approximation R h2 n K C
    hKC (A i) (hCells i).1 (hCells i).2.2 m hMN (v i) delta hDelta.
  exists P; split; first exact: hPoly.
  split; first exact: hError.
  by rewrite hMassCell -EFinD in hMass.
have hDensitySum := @current_density_finite_sum_action R h2 n m Leb hLeb I
  (fun i x => @CharacteristicFunction.value R X (A i) x*:v i) S
  (fun i => @current_characteristic_density_action R h2 n m Leb hLeb
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) (A i) (hCells i).1 (v i)).
have hField : (fun x => \sum_i @CharacteristicFunction.value R X (A i) x*:v i)=value f.
  apply: funext=> x; rewrite hSum compact_summable_field_value_finite_sum.
  apply: eq_bigr=> i _; symmetry; exact: (@hValues i x).
rewrite hField in hDensitySum.
have hCurrent : T=\sum_i S i := current_density_action_unique hT hDensitySum.
have hMassT : M T=(size f)%:E := compact_summable_ambient_density_mass hT.
have [P [hPoly [hError hMass]]] := @polyhedral_finite_approximation_budget R h2 n m
  Full hFull C I S (fun i => size (w i)) hPieces epsilon hEpsilon.
exists P; split; first exact: hPoly.
split; first by rewrite hCurrent.
by rewrite -hTotal EFinD -hMassT in hMass.
Qed.
End FiniteImagePolyhedralApproximation.
