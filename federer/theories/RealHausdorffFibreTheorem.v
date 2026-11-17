(** Federer 2.10.25, pp. 188-189: the original fibre upper-integral
    estimate for every nonnegative real pair of degrees and the actual
    least Lipschitz constant. No fibre measurability is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffFibreCost
  RealHausdorffFibreNormalisation RealHausdorffFibreCutoffs
  RealHausdorffFibreIntegralBound LipschitzUP LipschitzConstant
  PartialFunctionBasic MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_25_real]: direct original theorem of
    Federer 2.10.25, pp. 188-189. Retain every nonnegative real k,m,
    the actual least Lipschitz constant, and the printed alternative
    finite-measure support or boundedly compact target hypothesis.
    The coefficient has the original Gamma-normalized value, including
    zero degree and zero Lipschitz bound. A need not be measurable. *)
Theorem federer_2_10_25_real (R : realType) (X Y : metricType R)
    (f : X -> Y) (hf : is_metric_lipschitz setT f) (k m : R)
    (hk : (0<=k)%R) (hm : (0<=m)%R) (A : set X) :
    real_hausdorff_fibre_integral_condition f A hk hm ->
    measure_upper_integral (@real_hausdorff_measure R Y m hm)
      (partial_function_total (real_hausdorff_fibre_mass f A hk))<=
    (real_hausdorff_fibre_bound_constant hk hm (metric_lipschitz_constant hf))%:E*
      @real_hausdorff_measure R X (k+m)%R (addr_ge0 hk hm) A.
Proof.
exact: real_hausdorff_lipschitz_fibre_integral_bound
  (least_metric_lipschitz_bound (metric_lipschitz_constant_specification hf)).
Qed.
