(** Federer (1969), 2.4.12, pp. 86–87: scalar closure of the finite-p
    Lebesgue spaces. This supporting membership law keeps the exact partial
    domain, including scalar zero. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasurableNormedArithmetic MeasureLpMembershipUP MeasureLpNorm MeasureLpNormScale
  MeasureLpCountableMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_lp_function_scale]: supporting full Lp
    membership of a scalar multiple in Federer 2.4.12, pp. 86–87.
    The finite-p countable-measurability condition follows from finite norm. *)
Lemma measure_lp_function_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p c : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f -> is_measure_lp_function mu p (partial_vector_scale c f).
Proof.
move=> hf.
have hA := @measurable_normed_function_scale R X V N hN mu hm c f hf.2.1.
have hn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hf.1 hf.2.1.1.
have hfin : measure_lp_norm mu N p f \is a fin_num by rewrite (ge0_fin_numE hn); exact hf.2.2.1.
have he : measure_lp_norm mu N p f = (fine (measure_lp_norm mu N p f))%:E by rewrite fineK.
have hcf : measure_lp_norm mu N p (partial_vector_scale c f) < +oo.
  rewrite (@measure_lp_norm_scale R X V N hN mu hm p c f hf.1 hf.2.1.1) he -EFinM; exact: ltry.
split; first exact hf.1.
split=> //; split=> //.
exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p _ hf.1 hA.1 hcf).
Qed.
