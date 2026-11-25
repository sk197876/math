(** Federer (1969), 4.1.23, p. 379:
    changing one constant-vector measurable cell
    to its rectangular approximant has the
    exact symmetric-difference mass cost.
    The resulting current is the actual
    Lebesgue density current on the original
    full ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentSpaces CurrentCoefficientNorms
  CurrentDensityAction CurrentDensityArithmetic CurrentDensityUniqueness
  CurrentCharacteristicDensity CurrentMassSealed SmoothCompactSet
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  CompactSummableFieldSealed CompactSummableFieldLaws CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableFullCurrentAction
  CompactSummableAmbientFieldLift CompactCharacteristicSummableField
  CompactCharacteristicSetDifference MeasureUP MeasureBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CharacteristicDifference.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
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
Local Notation WA := (@CompactSummableField.space R XT V VN hVN Leb hLeb).
Local Notation value := (@compact_summable_field_value R XT V VN hVN Leb hLeb).
Local Notation size := (@compact_summable_field_size R XT V VN hVN Leb hLeb).
Local Notation C := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation cell := (fun A hA z => @current_characteristic_density R h2 n m
  Leb hLeb (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).

(** Source for [compact_summable_ambient_density_mass]:
    the actual current of an ambient
    compact L1 field has its original
    integral mass, supporting the cell
    and box errors of Federer
    4.1.23, p. 379. Representation
    is derived internally through Omega. *)
Theorem compact_summable_ambient_density_mass (f : WA) (T : C) :
  @is_current_density_action R h2 n m Leb (value f) T -> M T=(size f)%:E.
Proof.
move=> hT.
have [xi [hRaw hSize]] := @compact_summable_ambient_field_lift R h2 n m f.
have hXi := @compact_summable_full_current_action R h2 n m xi.
rewrite hRaw in hXi.
have hEqual : T=@compact_summable_multivector_current R h2 n m Full hFull xi.
  exact: (@current_density_action_unique R h2 n m Leb (value f) T _ hT hXi).
by rewrite hEqual compact_summable_multivector_current_mass hSize.
Qed.

(** Source for [characteristic_current_difference_mass]:
    M(Lebesgue wedge (1_A-1_B)z)
    equals mass(z) times the sum
    of the two one-sided set errors,
    supporting Federer 4.1.23, p. 379.
    Both original sets may be merely
    measurable and have null or empty parts. *)
Theorem characteristic_current_difference_mass (A B : set X)
    (hA : measure_measurable Leb A) (hB : measure_measurable Leb B) (z : V)
    (K : smooth_compact_set hNX Full)
    (hAK : A `<=` smooth_compact_carrier K)
    (hBK : B `<=` smooth_compact_carrier K) :
  M (cell A hA z-cell B hB z)=((VN z)%:E*(Leb (A `\` B)+Leb (B `\` A)))%E.
Proof.
have hKFinite := @euclidean_distribution_measure_compact_finite R n
  (smooth_compact_carrier K) (smooth_compact_is_compact K).
have hAFinite : (Leb A< +oo)%E := le_lt_trans (measure_mono hLeb hAK) hKFinite.
have hBFinite : (Leb B< +oo)%E := le_lt_trans (measure_mono hLeb hBK) hKFinite.
have [f [hF _]] := @compact_characteristic_summable_field_exists R XT V VN hVN Leb hLeb
  A hA hAFinite (smooth_compact_carrier K) (smooth_compact_is_compact K) hAK z.
have [g [hG _]] := @compact_characteristic_summable_field_exists R XT V VN hVN Leb hLeb
  B hB hBFinite (smooth_compact_carrier K) (smooth_compact_is_compact K) hBK z.
have hCost := @compact_characteristic_set_difference_cost R XT V VN hVN Leb hLeb
  A B z f g hA hB hAFinite hBFinite hF hG.
pose fa := fun x => @CharacteristicFunction.value R X A x*:z.
pose fb := fun x => @CharacteristicFunction.value R X B x*:z.
have hAT := @current_characteristic_density_action R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n) (@euclidean_distribution_measure_compact_finite R n)
  A hA z.
have hBT := @current_characteristic_density_action R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n) (@euclidean_distribution_measure_compact_finite R n)
  B hB z.
have hNegative := @current_density_scaled_action R h2 n m Leb hLeb fb (cell B hB z) (-1) hBT.
have hDifference := @current_density_sum_action R h2 n m Leb hLeb fa
  (fun x => (-1)*:fb x) (cell A hA z) ((-1)*:cell B hB z) hAT hNegative.
rewrite scaleN1r in hDifference.
have hField : value (f-g)=(fun x => fa x+(-1)*:fb x).
  apply: funext=> x; rewrite compact_summable_field_value_difference
    (@hF x) (@hG x) scaleN1r.
  reflexivity.
rewrite -hField in hDifference.
rewrite (@compact_summable_ambient_density_mass (f-g) _ hDifference).
exact: hCost.
Qed.
End CharacteristicDifference.
