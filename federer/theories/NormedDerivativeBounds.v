(** Federer (1969), 2.9.22, pp. 167–168: derivative bounds from Lipschitz
    estimates and the zero arc-length-derivative case. The norm is specified
    abstractly. Chapter 21 has no matching reflexive Banach extension. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormMetricContinuity NormedCurveDerivativeUP
  RealCurveDerivativeUP RealDerivativeOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_norm_limit_norm]: supporting passage
    to norms in Federer 2.9.22, pp. 167–168. The reverse
    triangle inequality makes the scalar norms converge to N(v). *)
Lemma punctured_norm_limit_norm (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (u : R -> E) v :
  punctured_norm_limit N u v ->
  punctured_real_limit (fun h => N (u h)) (N v).
Proof.
move=> hu e he; have [d [hd hB]] := hu e he.
exists d; split=> // h hh.
exact: le_lt_trans (real_norm_change_bound hN _ _) (hB h hh).
Qed.

(** Source for [normed_curve_derivative_lipschitz_bound]: the
    bound |v(x)|<=Lip(g) in Federer 2.9.22, p. 167,
    for an actual norm derivative. This necessary estimate does
    not assert existence of derivatives for arbitrary Banach spaces. *)
Lemma normed_curve_derivative_lipschitz_bound (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (L x : R) v :
  (forall t u, N (g t-g u)<=L*`|t-u|) ->
  has_normed_curve_derivative N g x v -> N v<=L.
Proof.
move=> hL hv.
apply: (@punctured_real_limit_order R (fun h => N (h^-1 *: (g (x+h)-g x)))
  (fun _ => L) (N v) L (punctured_norm_limit_norm hN hv)
  (punctured_real_constant_limit L))=> h hn.
rewrite (real_seminorm_scale hN.1) normfV.
have hb := hL (x+h) x.
rewrite addrAC subrr add0r in hb.
have hh : 0<`|h| by rewrite normr_gt0.
by rewrite mulrC ler_pdivrMr.
Qed.

(** Source for [normed_curve_zero_derivative_from_control]: the
    first alternative on Federer 2.9.22, p. 168: if the
    scalar parameter has derivative zero and controls the curve's
    distance, the curve has norm derivative zero. Reflexivity is
    unnecessary for this local implication. *)
Lemma normed_curve_zero_derivative_from_control (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (g : R -> E) (s : R -> R) x :
  (forall h, N (g (x+h)-g x)<=`|s (x+h)-s x|) ->
  has_real_curve_derivative s x 0 -> has_normed_curve_derivative N g x 0.
Proof.
move=> hc hs e he; have [d [hd hB]] := hs e he.
exists d; split=> // h hh.
have hb := hB h hh.
rewrite subr0 normrM normfV in hb.
rewrite subr0 (real_seminorm_scale hN.1) normfV.
apply: le_lt_trans _ hb.
have hinv : 0<=`|h|^-1 by rewrite invr_ge0 normr_ge0.
have hscale := ler_wpM2l hinv (hc h).
by rewrite [X in _<=X]mulrC in hscale.
Qed.
