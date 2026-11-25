(** Federer (1969), 3.1.1, p. 211: evaluations on the space Z of
    continuous linear maps are continuous. These consequences use
    only the abstract evaluation and least-bound norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormOperatorNormUP
  ContinuousOperatorUP ContinuousOperatorNorm NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Evaluation.
Variable R : realType.
Variables X Y Z : lmodType R.
Variable NX : X -> R.
Variable NY : Y -> R.
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : Hom Z (Hom X Y).
Variable ZN : Z -> R.
Hypothesis hZ : is_continuous_operator_space NX NY evaluation ZN.
Let hZN := continuous_operator_norm_is_norm hNY hZ.

(** Source for [continuous_operator_evaluation_distance]: the
    operator-norm bound for a fixed evaluation, supporting the
    topology of Z in 3.1.1, p. 211. *)
Lemma continuous_operator_evaluation_distance x
    (z w : real_norm_metric_space hZN) :
  mdist (evaluation z x : real_norm_metric_space hNY) (evaluation w x)
    <= NX x * mdist z w.
Proof.
change (NY (evaluation z x-evaluation w x)<=NX x*ZN (z-w)).
have hb := norm_operator_bound (continuous_operator_norm_laws hZ (z-w)) x.
by rewrite linearB /= mulrC in hb.
Qed.

(** Source for [continuous_operator_evaluation_continuous]:
    continuous evaluations support the closed remainder tests in
    Federer's Borel differential argument, 3.1.1, p. 211. *)
Lemma continuous_operator_evaluation_continuous x :
  continuous (fun z : real_norm_metric_space hZN =>
    (evaluation z x : real_norm_metric_space hNY)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ (NX x)
  (real_seminorm_nonnegative hNX.1 x)).
exact: continuous_operator_evaluation_distance.
Qed.
End Evaluation.
