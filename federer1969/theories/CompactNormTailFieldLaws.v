(** Federer (1969), 4.1.5, p. 350: the actual
    continuous cutoff splits w into h w and w-h w.
    Their exact norms give the positive-tail and small
    remainder estimates in the printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP CompactNormTailUP
  NormTailScalarLaws CompactContinuousDomainFields CompactContinuousFieldMultiplier.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactNormTailFieldLaws.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable w:X->Y.
Variable eta:R.
Variable h:X->R.
Hypothesis hH:is_compact_norm_tail_cutoff NY w eta h.

(** Source for [compact_norm_tail_field_norm]: the original
    norm of h w is the positive tail in Federer
    4.1.5, p. 350. *)
Lemma compact_norm_tail_field_norm x:
  NY (h x*:w x)=Num.max (NY (w x)-eta) 0.
Proof.
have hNonnegative:0<=h x:=(andP (compact_norm_tail_range hH x)).1.
by rewrite (real_seminorm_scale hNY.1) (ger0_norm hNonnegative) (compact_norm_tail_product hH x).
Qed.

(** Source for [compact_norm_tail_remainder_norm]: the norm
    of w-h w is exactly the removed tail, supporting
    the second original estimate in Federer 4.1.5,
    p. 350. *)
Lemma compact_norm_tail_remainder_norm x:
  NY (w x-h x*:w x)=NY (w x)-Num.max (NY (w x)-eta) 0.
Proof.
have hUpper:h x<= 1:=(andP (compact_norm_tail_range hH x)).2.
have hCoefficient:0<=1-h x by lra.
have hDiff:w x-h x*:w x=(1-h x)*:w x by rewrite scalerBl scale1r.
by rewrite hDiff (real_seminorm_scale hNY.1) (ger0_norm hCoefficient)
  mulrBl mul1r (compact_norm_tail_product hH x).
Qed.

(** Source for [compact_norm_tail_remainder_bound]: the
    original uniform eta bound on the removed vector
    tail in Federer 4.1.5, p. 350. *)
Lemma compact_norm_tail_remainder_bound:0<eta ->
  forall x,NY (w x-h x*:w x)<=eta.
Proof.
move=>hEta x; rewrite compact_norm_tail_remainder_norm.
exact:(andP (@norm_tail_scalar_ratio_laws R (NY (w x)) eta
  (real_seminorm_nonnegative hNY.1 (w x)) hEta).2.2.2).2.
Qed.

(** Source for [compact_norm_tail_field_inside]: h w
    belongs to the actual compact continuous extension
    domain, Federer 4.1.5, p. 350. *)
Lemma compact_norm_tail_field_inside U:
  compact_continuous_domain_fields U hNY w ->
  compact_continuous_domain_fields U hNY (fun x=>h x*:w x).
Proof.
move=>hw; exact:(@compact_continuous_field_multiplier R X U Y NY hNY w h hw
  (compact_norm_tail_function hH).1).
Qed.
End CompactNormTailFieldLaws.
