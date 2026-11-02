(** Federer (1969), 2.4.15, printed p. 89: Minkowski's inequality for finite
    p>1. This module proves the principal inequality following the book's
    preliminary summability, conjugate power, two Holder estimates, and
    cancellation. The general and inner-product equality criteria are
    separate assertions. Completeness of the normed target is not needed for
    the inequality itself. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MeasureLpNorm MeasureLpMembershipUP MeasureLpSumMembership MeasureMinkowskiPowerEstimate MinkowskiScalarBound MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_inequality]: the principal inequality of Federer
    2.4.15, p. 89 Both functions belong to the project's partial-domain Lp
    space. The proof first establishes Lp membership of their sum and
    handles its zero norm separately before cancellation. *)
Theorem minkowski_inequality (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  measure_lp_norm mu N p (partial_vector_add f g) <= measure_lp_norm mu N p f + measure_lp_norm mu N p g.
Proof.
move=> hp hf hg.
have hs := @measure_lp_function_add R X V N hN mu hm p f g hf hg.
have hfnn := @measure_lp_norm_nonnegative R X V N hN mu p f hm hf.1 hf.2.1.1.
have hgnn := @measure_lp_norm_nonnegative R X V N hN mu p g hm hg.1 hg.2.1.1.
have hsnn := @measure_lp_norm_nonnegative R X V N hN mu p _ hm hs.1 hs.2.1.1.
have hffin : measure_lp_norm mu N p f \is a fin_num.
  rewrite (ge0_fin_numE hfnn); exact hf.2.2.1.
have hgfin : measure_lp_norm mu N p g \is a fin_num.
  rewrite (ge0_fin_numE hgnn); exact hg.2.2.1.
have hsfin : measure_lp_norm mu N p (partial_vector_add f g) \is a fin_num.
  rewrite (ge0_fin_numE hsnn); exact hs.2.2.1.
pose a := fine (measure_lp_norm mu N p f).
pose b := fine (measure_lp_norm mu N p g).
pose c := fine (measure_lp_norm mu N p (partial_vector_add f g)).
have hfa : measure_lp_norm mu N p f = a%:E by rewrite fineK.
have hgb : measure_lp_norm mu N p g = b%:E by rewrite fineK.
have hsc : measure_lp_norm mu N p (partial_vector_add f g) = c%:E by rewrite fineK.
have ha0 : (0 <= a)%R by move: hfnn; rewrite hfa lee_fin.
have hb0 : (0 <= b)%R by move: hgnn; rewrite hgb lee_fin.
have hc0 : (0 <= c)%R by move: hsnn; rewrite hsc lee_fin.
have hpow := @measure_minkowski_power_estimate R X V N hN mu hm p a b c f g hp hf.2.1 hg.2.1 hfa hgb hsc.
rewrite hfa hgb hsc -EFinD lee_fin.
exact (@minkowski_power_bound_cancel R p c (a+b)%R hp hc0 (addr_ge0 ha0 hb0) hpow).
Qed.
