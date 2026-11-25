(** Federer (1969), 3.1.11, p. 220:
    norm and completeness consequences for the abstract
    continuous-endomorphism algebra, proved from its public laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom AlgebraUP RealNormUP NormMetric NormOperatorNormUP
  ContinuousOperatorUP ContinuousOperatorNorm ContinuousOperatorBanach
  ContinuousOperatorAlgebraUP CompleteMetricUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section AlgebraLaws.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.
Variable A : algebra R.
Variable evaluation : Hom A (Hom X X).
Variable AN : A->R.
Hypothesis hA : is_continuous_operator_algebra NX evaluation AN.

(** Source for [operator_algebra_norm_is_norm]: the
    operator norm on E is a norm, as required in
    Federer 3.1.11, p. 220. *)
Lemma operator_algebra_norm_is_norm : is_real_norm AN.
Proof. exact (continuous_operator_norm_is_norm hNX (operator_algebra_space hA)). Qed.

(** Source for [operator_algebra_norm_product]: submultiplicativity
    of the operator norm, supporting the inverse series
    in Federer 3.1.11, p. 220. *)
Lemma operator_algebra_norm_product u v : AN (alg_mul A u v)<=AN u*AN v.
Proof.
pose hE := operator_algebra_space hA.
apply: (norm_operator_least (continuous_operator_norm_laws hE (alg_mul A u v))).
- exact: mulr_ge0 (norm_operator_nonnegative (continuous_operator_norm_laws hE u))
    (norm_operator_nonnegative (continuous_operator_norm_laws hE v)).
- move=> x; rewrite (operator_algebra_composition hA) hom_compE.
  apply: le_trans (norm_operator_bound (continuous_operator_norm_laws hE u) (evaluation v x)) _.
  have hh := ler_wpM2l (norm_operator_nonnegative (continuous_operator_norm_laws hE u))
    (norm_operator_bound (continuous_operator_norm_laws hE v) x).
  by rewrite mulrA in hh.
Qed.

(** Source for [operator_algebra_norm_identity]: the
    identity has norm at most one, supporting the constant
    term of the inverse series in Federer 3.1.11,
    p. 220. This includes the zero source, whose identity is zero. *)
Lemma operator_algebra_norm_identity : AN (alg_one A)<= 1.
Proof.
apply: (norm_operator_least
  (continuous_operator_norm_laws (operator_algebra_space hA) (alg_one A)) ler01).
move=> x.
by rewrite (operator_algebra_identity hA) hom_of_linearE /= mul1r.
Qed.

(** Source for [operator_algebra_complete]: E is a Banach
    space when X is Banach, Federer 3.1.11, p. 220.
    No finite-dimensional restriction is imposed. *)
Theorem operator_algebra_complete :
  is_complete_metric_space (real_norm_metric_space hNX) ->
  is_complete_metric_space (real_norm_metric_space operator_algebra_norm_is_norm).
Proof.
exact (@continuous_operator_complete_general R X X A NX NX hNX hNX
  evaluation AN (operator_algebra_space hA)).
Qed.
End AlgebraLaws.
