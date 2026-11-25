(** Federer (1969), 2.4.12, pp. 87–88: sealed integral on finite-image L1
    functions. Only the abstract dual-evaluation specification is exposed;
    no enumeration or fibre sum is public. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureStepFunctionUP
  MeasureLpMembershipUP MeasureVectorIntegralUP FiniteVectorIntegralConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.
Module Type FiniteVectorIntegralSignature.
(** Source for [value]: abstract finite-image integral used in Federer
    2.4.12, pp. 87–88 *)
Parameter value : forall (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN)),
  is_measure_lp_function mu 1%R f -> finite_set (partial_function_range f) -> V.
(** Source for [laws]: the selected vector satisfies Federer's
    integral specification, 2.4.12, pp. 87–88. *)
Parameter laws : forall (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN))
  (hf : is_measure_lp_function mu 1%R f) (hfinite : finite_set (partial_function_range f)),
  is_measure_vector_integral mu f (@value R X V N hN mu hm f hf hfinite).
End FiniteVectorIntegralSignature.
Module FiniteVectorIntegral : FiniteVectorIntegralSignature.
(** Source for [value]: private selection of a proved integral
    witness for Federer 2.4.12, pp. 87–88. *)
Definition value (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN))
  (hf : is_measure_lp_function mu 1%R f) (hfinite : finite_set (partial_function_range f)) :=
  projT1 (cid (@finite_vector_integral_exists R X V N hN mu hm f hf hfinite)).
(** Source for [laws]: the witness proves the exposed dual
    specification supporting Federer 2.4.12, pp. 87–88. *)
Lemma laws (R : realType) (X : choiceType)
  (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
  (mu : set X -> \bar R) (hm : is_measure mu)
  (f : partial_function X (real_norm_metric_space hN))
  (hf : is_measure_lp_function mu 1%R f) (hfinite : finite_set (partial_function_range f)) :
  is_measure_vector_integral mu f (@value R X V N hN mu hm f hf hfinite).
Proof. exact: projT2 (cid (@finite_vector_integral_exists R X V N hN mu hm f hf hfinite)). Qed.
End FiniteVectorIntegral.
