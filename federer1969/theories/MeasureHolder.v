(** Federer (1969), 2.4.14, printed p. 88: Holder's inequality and its
    signed-power equality criterion. This public theorem uses the project's
    partial-domain Lp membership predicate and proved integral and norm
    interfaces. The finite exponents include Federer's printed weak lower
    bounds, which the reciprocal identity forces to be strict. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialScalarProduct
  MeasureSignedPowerDependenceUP MeasureHolderScalar MeasureHolderEquality
  MeasureLpNorm MeasureLpMembershipUP MeasureUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [holder_inequality_and_equality]: direct formalisation of
    Federer 2.4.14, p. 88 For finite conjugate exponents and f in Lp, g in
    Lq, the product is summable, its absolute integral is bounded by the
    product of the norms, and equality holds exactly for almost linear
    dependence of the signed powers. Zero norms and partial conull domains
    are included. *)
Theorem holder_inequality_and_equality (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (p^-1 + q^-1 = 1)%R ->
  is_measure_lp_function mu p f -> is_measure_lp_function mu q g ->
  exists c : R, is_measure_integral mu (partial_scalar_product f g) c%:E /\
    `|c|%:E <= measure_lp_norm mu (fun x : R => `|x|%R) p f * measure_lp_norm mu (fun x : R => `|x|%R) q g /\
    (`|c|%:E = measure_lp_norm mu (fun x : R => `|x|%R) p f * measure_lp_norm mu (fun x : R => `|x|%R) q g <->
      is_almost_signed_power_dependent mu p q f g).
Proof.
move=> hpq hf hg.
have hfnn := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu p f hm hf.1 hf.2.1.1.
have hgnn := @measure_lp_norm_nonnegative R X R^o _ (scalar_absolute_value_norm R) mu q g hm hg.1 hg.2.1.1.
have hffin : measure_lp_norm mu (fun x : R => `|x|%R) p f \is a fin_num.
  rewrite (ge0_fin_numE hfnn); exact hf.2.2.1.
have hgfin : measure_lp_norm mu (fun x : R => `|x|%R) q g \is a fin_num.
  rewrite (ge0_fin_numE hgnn); exact hg.2.2.1.
pose a := fine (measure_lp_norm mu (fun x : R => `|x|%R) p f).
pose b := fine (measure_lp_norm mu (fun x : R => `|x|%R) q g).
have hfa : measure_lp_norm mu (fun x : R => `|x|%R) p f = a%:E by rewrite fineK.
have hgb : measure_lp_norm mu (fun x : R => `|x|%R) q g = b%:E by rewrite fineK.
have [c [hci hc]] := @measure_holder_scalar_finite R X mu hm p q a b f g
  hf.1 hg.1 hpq hf.2.1.1 hg.2.1.1 hfa hgb.
have heq := @measure_holder_equality_iff R X mu hm p q a b c f g
  hf.1 hg.1 hpq hf.2.1.1 hg.2.1.1 hfa hgb hci.
exists c; split=> //; rewrite hfa hgb -EFinM; split; first by rewrite lee_fin.
split.
- move=> he; apply: heq.1; exact (EFin_inj he).
- move=> he; by rewrite (heq.2 he).
Qed.
