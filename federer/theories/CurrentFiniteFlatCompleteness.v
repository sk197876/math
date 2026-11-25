(** Federer (1969), 4.1.12, p. 367: the
    actual currents with finite F_K form a complete
    normed space. Reuse the abstract bounded-operator
    completeness theorem with the original test seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentFlatNorm
  CurrentFlatFormSeminormLaws CurrentFiniteFlatSpace CurrentFiniteFlatOperator
  ContinuousOperatorNorm CompleteMetricUP ScalarNormMetricCompleteness SeminormOperatorBanach.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFiniteFlatCompleteness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation B := (@finite_flat_current_space R h2 n m U hU K).
Local Notation F := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation N := (@finite_flat_current_norm R h2 n m U hU K).
Local Notation evaluation := (@finite_flat_current_evaluation R h2 n m U hU K).
Local Notation hB := (@finite_flat_current_operator_space_laws R h2 n m U hU K).

(** Source for [finite_flat_current_norm_is_norm]: the
    original finite dual flat seminorm is a norm
    on actual currents, supporting Federer 4.1.12,
    p. 367. Test evaluation separates currents. *)
Theorem finite_flat_current_norm_is_norm:is_real_norm N.
Proof. exact:(continuous_operator_norm_is_norm (@scalar_absolute_value_norm R) hB). Qed.

(** Source for [finite_flat_current_complete]: the original
    D_m(U) intersect {T:F_K(T)<infinity} is F_K-complete,
    Federer 4.1.12, p. 367. The test source may
    have a nontrivial seminorm kernel; only scalar
    target completeness is required. *)
Theorem finite_flat_current_complete:
  is_complete_metric_space (real_norm_metric_space finite_flat_current_norm_is_norm).
Proof.
have hNorm:finite_flat_current_norm_is_norm=
    continuous_operator_norm_is_norm (@scalar_absolute_value_norm R) hB:=Prop_irrelevance _ _.
rewrite hNorm.
exact:(@seminorm_operator_complete R DT R^o B F (fun a:R^o=>`|a|)
  (@current_flat_test_is_seminorm R h2 n m U hU K) (@scalar_absolute_value_norm R)
  evaluation N hB (@scalar_norm_metric_complete R)).
Qed.
End CurrentFiniteFlatCompleteness.
