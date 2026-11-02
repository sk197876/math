(** Federer (1969), 3.1.1, p. 211: existence of all partial derivatives
    at a point need not imply differentiability there. The book does not
    specify an example in this sentence. The explicit witness below is
    xy/(x^2+y^2), extended by zero at the origin. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLocal NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_derivative_counterexample]: an explicit witness
    for the nonimplication stated in Federer 3.1.1, p. 211; this particular
    rational formula is not printed there. The field convention 0^-1=0
    defines its value at the origin as zero. *)
Definition partial_derivative_counterexample (R : realType) (p : R * R) : R :=
  (p.1 * p.2)/(p.1^+2 + p.2^+2).

(** Source for [partial_derivative_counterexample_axes]: supporting
    verification of the example for Federer 3.1.1, p. 211: both coordinate
    restrictions are identically zero, so both partial derivatives exist. *)
Lemma partial_derivative_counterexample_axes (R : realType) :
  has_normed_curve_derivative (fun t : R^o => `|t|)
    (fun t => partial_derivative_counterexample (t,0)) 0 0 /\
  has_normed_curve_derivative (fun t : R^o => `|t|)
    (fun t => partial_derivative_counterexample (0,t)) 0 0.
Proof.
split.
- move=> e he; exists 1; split; first exact: ltr01.
  move=> t _; by rewrite /partial_derivative_counterexample /= !mulr0 !mul0r
    subrr scaler0 subrr normr0.
- move=> e he; exists 1; split; first exact: ltr01.
  move=> t _; by rewrite /partial_derivative_counterexample /= !mul0r
    subrr scaler0 subrr normr0.
Qed.

(** Source for [partial_derivative_counterexample_diagonal]: supporting
    diagonal evaluation of the counterexample to the implication discussed
    in Federer 3.1.1, p. 211: every nonzero diagonal point has value 1/2. *)
Lemma partial_derivative_counterexample_diagonal (R : realType) (t : R) :
  t != 0 -> partial_derivative_counterexample (t,t) = 1/2.
Proof.
move=> ht; rewrite /partial_derivative_counterexample /= !expr2.
have he : t*t+t*t = (t*t)*2 by ring.
rewrite he invfM mulrA divff ?mul1r //.
by rewrite mulf_eq0 (negbTE ht).
Qed.

(** Source for [partial_derivatives_not_differentiable]: the asserted
    nonimplication in Federer 3.1.1, p. 211, witnessed at the origin by
    the two coordinate derivatives above and failure of differentiability.
    This proof works for every supplied norm on the real plane, including
    its usual Euclidean norm. *)
Theorem partial_derivatives_not_differentiable (R : realType)
    (NX : R^o * R^o -> R) (hNX : is_real_norm NX) :
  ~ norm_differentiable_at NX
    (fun t : R^o => `|t|) (fun _ => True) (@partial_derivative_counterexample R) (0,0).
Proof.
move=> [L hf].
have he : 0 < (1/4 : R) by rewrite divr_gt0 // ltr0n.
have [d [hd hb]] := norm_differential_continuous_at (@scalar_absolute_value_norm R) hf he.
pose v : R^o * R^o := (1,1).
pose t := d/(2*(NX v+1)).
have hn := real_seminorm_nonnegative hNX.1 v.
have hn1 : 0 < NX v+1 by lra.
have ht : 0 < t by rewrite /t divr_gt0 // mulr_gt0 // ltr0n.
have hbound : NX (t *: v) < d.
  rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
  have hcoef : t*(NX v+1)=d/2.
    rewrite /t invfM mulrA.
    by rewrite divfK // gt_eqF.
  have hsmall : t*NX v < t*(NX v+1) by rewrite ltr_pM2l // ltrDl.
  rewrite hcoef in hsmall; have hhalf : d/2 < d by lra.
  exact: lt_trans hsmall hhalf.
have h := hb (t *: v) I hbound.
have hscaled : t *: v = (t,t).
  change ((t*1,t*1)=(t,t)); by rewrite !mulr1.
rewrite add0r hscaled in h.
change (is_true (`|partial_derivative_counterexample (t,t)-
  partial_derivative_counterexample (0,0)| < 1/4)) in h.
rewrite (partial_derivative_counterexample_diagonal (lt0r_neq0 ht)) in h.
have hzero : partial_derivative_counterexample (0:R,0) = 0.
  by rewrite /partial_derivative_counterexample /= !mul0r.
rewrite hzero subr0 in h.
have hh : 0 <= (1/2 : R) by rewrite divr_ge0 // ler0n.
rewrite (ger0_norm hh) in h; by lra.
Qed.
