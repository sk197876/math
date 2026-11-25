(** De Philippis, Gennaioli, Pigati and Rindler (2026), Lemma 3.1;
    blueprint dgpr_blueprint.tex, lem:DGPR31:
      ∫_0^T ∫ rho_t (|DB_t|^2 + |B_t(grad log rho_t)|^2) dL^n dL^1 t
        <= C gamma (1 + log((1 + T^(1/2) delta)/gamma)),
    with C = (16 n + 6) Lambda^2 + 16, under (S) alone. The Gaussian
    decay before T of rho log q and of rho |B|^2 (lem:regularity,
    DgprRegularity.v) discharges the hypotheses [hJgauss] and [hKgauss]
    of [dgpr_lemma_3_1_conditional] (DgprLemma31Final.v). The field DB is
    any field with the values of D B_t(x) for t < T; such a field exists
    by [dgpr_lemma31_DB_exists] (DgprLemma31Field.v). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  LinearBasis HomInner HomInnerCoordinates ScalarInnerProduct ProductInner TensorUP Bilinear
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralBounds SummableRealFunctionUP SummableRealArithmetic RadonMeasureUP
  EuclideanLebesgueDimensions LebesgueScalarMeasure ScalarNormMetricCompleteness LocalUniquenessExample
  NormDifferentialUP NormClassOneUP NormRegularity SmoothFunctionSpaceUP SmoothTestSpaces
  RealExponentialUP RealExponentialSealed RealExponentialLaws.
From DPGPR Require Import DgprDifferentialCalculus DgprStanding DgprHeatObjects DgprLemma31Main
  DgprLemma31Final DgprRegularity DgprLemma31Field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Lemma31Theorem.
Variable R : realType.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation TX := ((R^o * R_n R n)%type).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation heX := (@coordinate_basisP R n).
Variable Y : lmodType R.
Variable CY : Y -> Y -> R.
Hypothesis hCY : is_inner_product CY.
Variable d : nat.
Variable eY : 'I_d -> Y.
Hypothesis heY : is_basis eY.
Hypothesis hm : (0 < m <= n)%N.
Local Notation NY := (inner_norm hCY).
Local Notation hNY := (inner_norm_real_norm hCY).
Local Notation BH := (hom_inner_productP BX hCY heX).
Local Notation NH := (hom_norm BX hCY heX).
Local Notation hNH := (inner_norm_real_norm BH).
Variable K : set (real_norm_metric_space hNH).
Variables lam Lam : R.
Variable mu : set X -> \bar R.
Variable r0 : R.
Variable Xf : X -> Hom X Y.
Variable E : lmodType R.
Variable ev : E -> X -> Y.
Hypothesis hE : is_smooth_function_space hN hNY setT ev.
Variable Ups : Hom (smooth_test_space hE) R^o.
Variable ups : set (real_norm_metric_space hN) -> \bar R.
Variable dups : X -> Hom Y R^o.
Variable delta : R.
Variable T : R.
Variable mu0 : set X -> \bar R.
Variable gamma : R.
Hypothesis hS : dgpr_standing heY hm K lam Lam mu r0 Xf Ups ups dups delta T mu0 gamma.
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation L1 := (@lebesgue_scalar_measure R).
Local Notation B := (dgpr_heat_B hS).
Local Notation LOG := (@RealExponential.logarithm R).

(** Source for [dgpr_lemma_3_1]: DPGPR 2026, Lemma 3.1, and blueprint
    lem:DGPR31: [dgpr_lemma_3_1_conditional] with the Gaussian decay
    before T of rho log q and rho |B|^2 from lem:regularity
    ([dgpr_regularity_entropy_gaussian], [dgpr_regularity_B2_gaussian]). *)
Theorem dgpr_lemma_3_1 (DB : TX -> X -> Hom X Y) :
  (forall t x, t < T -> dgpr_differential_values NH (fun z => B (t, z)) x (DB (t, x))) ->
  (measure_subset_upper_integral L1 [set t : R | (0 <= t < T)%R]
     (partial_function_total (fun t : R => measure_upper_integral LL
        (real_total_integrand (fun x => dgpr_lemma31_integrand hS DB (t, x)))))
   <= (((16 * n%:R + 6) * Lam ^+ 2 + 16) * gamma * (1 + LOG ((1 + Num.sqrt T * delta) / gamma)))%:E)%E.
Proof.
move=> hDB.
exact (dgpr_lemma_3_1_conditional hDB (dgpr_regularity_entropy_gaussian hS)
  (dgpr_regularity_B2_gaussian hS)).
Qed.
End Lemma31Theorem.
