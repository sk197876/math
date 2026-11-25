(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    lem:compact_case: the statement of the compact case as a proposition
    on the numbers λ, Λ and C, for the data of mr:hypotheses_main
    ([dgpr_main_hypotheses], DgprMainHypotheses.v) whose measure
    μ = (H^k ⌞ M) ⌞ θ vanishes outside a closed ball B(0, r_0). This
    file fixes the interface between the proof of lem:compact_case for
    such data and the proof of thm:main by cut-off functions; it contains
    no proof. The support condition is stated as in DgprStanding.v:
    |y| ≤ r_0 for μ almost all y. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates LinearBasis HomInner InnerConvex
  InnerMetric PartialFunctionUP PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureRestriction
  MeasureDensity MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP RadonMeasureUP
  FunctionLatticeUP CompactSupportFunctionUP DistributionVariationUP SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation NormDifferentialUP HausdorffMeasure RectifiableSetUP
  TopologicalBorel RealPower.
From DPGPR Require Import DgprMainHypotheses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactCaseInequality.

Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.

Local Notation X := (R_n R n).
Local Notation BX := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm BX).
Local Notation hN := (inner_norm_real_norm BX).
Local Notation RnM := (inner_metric_space BX).
Local Notation HK := (@hausdorff_measure R RnM k).

(** Source for [dgpr_compact_case_inequality]: blueprint
    lem:compact_case, the conclusion for the numbers λ, Λ and C: whenever
    Y is a finite dimensional inner product space, the data of
    mr:hypotheses_main are given with these λ and Λ, and
    μ(R^n ∖ B(0, r_0)) = 0 for some 0 < r_0 < ∞, then
    μ(R^n) ≤ C H^k(M)^{1/k} ‖Υ‖(R^n). Definition. *)
Definition dgpr_compact_case_inequality (lam Lam C : R) : Prop :=
  forall (Y : lmodType R) (CY : Y -> Y -> R) (hCY : is_inner_product CY)
    (d : nat) (eY : 'I_d -> Y) (E : lmodType R) (ev : E -> X -> Y)
    (hE : is_smooth_function_space hN (inner_norm_real_norm hCY) setT ev)
    K M (theta : X -> R) (Xf : X -> Hom X Y) (Ups : Hom (smooth_test_space hE) R^o)
    (ups : set (real_norm_metric_space hN) -> \bar R),
  @dgpr_main_hypotheses R n k hk Y CY hCY d eY E ev hE K lam Lam M theta Xf Ups ups ->
  (exists r0 : R, 0 < r0 /\
    measure_almost_everywhere (dgpr_main_measure k M theta) [set y | N y <= r0]) ->
  (dgpr_main_measure k M theta setT <=
    (C * real_power (fine (HK M)) (k%:R)^-1)%:E * ups setT)%E.

End CompactCaseInequality.
