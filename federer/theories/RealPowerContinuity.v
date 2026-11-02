(** Federer (1969), 2.7.16, printed p. 139, example (6): "Whenever n >= m
    are positive integers and 1 <= t < oo, there exists a positive number
    beta_t(n, m) such that (int |(Lambda_m p) xi|^t dtheta*_{n,m} p)^{1/t} =
    beta_t(n, m) . |xi|". The integrand is the t-th power of a continuous
    nonnegative function. This module supplies the scalar facts used to
    treat it as a member of K(O*(n, m)) (2.5.13, p. 106): x |-> x^t is
    continuous on {x : x >= 0} for t > 0, (x^2)^{t/2} = x^t, x^{-t} =
    (x^t)^{-1}, and x^t = y^t implies x = y for x, y >= 0. The real powers
    are those of 2.4.12, p. 86 (RealPower.v); continuity is deduced from
    their strict monotonicity and from the identity (x^{1/t})^t = x. The
    local erratum has no entry for p. 139. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower
  RealPowerSuccessor RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RealPowerContinuity.
Variable R : realType.

(** Source for [real_power_two]: x^2 = x x for x >= 0, supporting the
    integrand |(Lambda_m p) xi|^t of Federer 2.7.16, p. 139, written
    through the square of the norm. Supporting lemma. *)
Lemma real_power_two (x : R) : 0 <= x -> real_power x 2 = x ^+ 2.
Proof.
move=> hx; have [->|hx0] := eqVneq x 0.
  rewrite real_power_zero_base; [by rewrite expr2 mulr0|by rewrite pnatr_eq0].
have hxp : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
rewrite (_ : 2 = 1 + 1) // real_power_add_exponents_positive //.
by rewrite real_power_one_exponent // expr2.
Qed.

(** Source for [real_power_square_half]: (x^2)^{t/2} = x^t for x >= 0
    and t > 0, supporting the integrand |(Lambda_m p) xi|^t of Federer
    2.7.16, p. 139. Supporting lemma. *)
Lemma real_power_square_half (x t : R) : 0 <= x -> 0 < t -> real_power (x ^+ 2) (t / 2) = real_power x t.
Proof.
move=> hx ht; rewrite -real_power_two // real_power_positive_iterate //; last first.
  by rewrite divr_gt0.
by rewrite mulrC divfK // pnatr_eq0.
Qed.

(** Source for [real_power_negative_exponent]: x^{-t} = (x^t)^{-1} for
    x > 0, supporting the factor beta_t(n - k, m)^{-t} of Federer
    2.7.16, p. 139. Supporting lemma. *)
Lemma real_power_negative_exponent (x t : R) : 0 < x -> real_power x (- t) = (real_power x t)^-1.
Proof.
move=> hx; have hpos : real_power x t != 0 by rewrite gt_eqF // real_power_strictly_positive.
apply: (mulfI hpos); rewrite -real_power_add_exponents_positive // subrr.
by rewrite real_power_zero_exponent mulfV.
Qed.

(** Source for [real_power_injective]: x^t = y^t implies x = y for
    x, y >= 0 and t > 0, supporting "As a corollary we obtain the equation
    beta_t(n, m)/beta_t(n - k, m) = beta_t(n, k)/beta_t(n - m, k)",
    Federer 2.7.16, p. 139, where the t-th powers are compared.
    Supporting lemma. *)
Lemma real_power_injective (x y t : R) :
  0 <= x -> 0 <= y -> 0 < t -> real_power x t = real_power y t -> x = y.
Proof.
move=> hx hy ht he; apply/eqP; rewrite eq_le.
by rewrite -(real_power_order_embedding hx hy ht) -(real_power_order_embedding hy hx ht) he lexx.
Qed.

(** Source for [real_power_inverse_power]: (x^{1/t})^t = x for x >= 0
    and t > 0. Supporting lemma for the continuity below. *)
Lemma real_power_inverse_power (x t : R) : 0 <= x -> 0 < t -> real_power (real_power x t^-1) t = x.
Proof.
move=> hx ht; rewrite real_power_positive_iterate ?invr_gt0 //.
by rewrite mulVf ?gt_eqF // real_power_one_exponent.
Qed.

(** Source for [real_power_local_bound]: for x >= 0, t > 0 and e > 0
    there is d > 0 with |x^t - y^t| < e whenever y >= 0 and |x - y| < d.
    Supporting lemma for the continuity of the integrand of Federer
    2.7.16, p. 139. Proof: with A = x^t and hi = (A + e)^{1/t} one has
    x < hi and y < hi implies y^t < A + e; if e <= A, then
    lo = (A - e)^{1/t} < x and y > lo implies y^t > A - e. *)
Lemma real_power_local_bound (x t e : R) : 0 <= x -> 0 < t -> 0 < e ->
  exists2 d, 0 < d & forall y, 0 <= y -> `|x - y| < d -> `|real_power x t - real_power y t| < e.
Proof.
move=> hx ht he.
pose A := real_power x t.
have hA : 0 <= A := real_power_nonnegative x t.
have hti : 0 < t^-1 by rewrite invr_gt0.
have hAx : real_power A t^-1 = x by rewrite /A real_power_root_cancel.
pose hi := real_power (A + e) t^-1.
have hxhi : x < hi.
  rewrite -hAx; apply: real_power_strict_monotone hA _ hti; by rewrite ltrDl.
have hhi : real_power hi t = A + e.
  by rewrite /hi real_power_inverse_power // addr_ge0 // ltW.
have hup y : 0 <= y -> y < hi -> real_power y t < A + e.
  by move=> hy hyh; rewrite -hhi; exact: real_power_strict_monotone.
case: (ltrP A e)=> hAe.
- exists (hi - x); first by rewrite subr_gt0.
  move=> y hy hd; rewrite ltr_distlC; apply/andP; split.
  + apply: lt_le_trans (real_power_nonnegative y t); by rewrite subr_lt0.
  + apply: hup=> //; move: hd; rewrite ltr_distlC => /andP [_].
    by rewrite addrC subrK.
- have hAe0 : 0 <= A - e by rewrite subr_ge0.
  pose lo := real_power (A - e) t^-1.
  have hlox : lo < x.
    rewrite -hAx; apply: real_power_strict_monotone hAe0 _ hti; by rewrite ltrBlDr ltrDl.
  have hlo : real_power lo t = A - e by rewrite /lo real_power_inverse_power.
  exists (Num.min (x - lo) (hi - x)); first by rewrite lt_min !subr_gt0 hlox hxhi.
  move=> y hy; rewrite lt_min => /andP [h1 h2].
  rewrite ltr_distlC; apply/andP; split.
  + rewrite -hlo; apply: real_power_strict_monotone _ _ ht.
      exact: real_power_nonnegative.
    move: h1; rewrite ltr_distlC => /andP [+ _]; by rewrite opprB addrC subrK.
  + apply: hup=> //; move: h2; rewrite ltr_distlC => /andP [_].
    by rewrite addrC subrK.
Qed.

(** Source for [real_power_continuous_comp]: if g is a continuous
    nonnegative real function and t > 0, then x |-> g(x)^t is continuous,
    supporting the membership of the integrand of Federer 2.7.16, p. 139,
    in K(O*(n, m)) (2.5.13, p. 106). Supporting lemma. *)
Lemma real_power_continuous_comp (X : topologicalType) (g : X -> R) (t : R) :
  continuous (g : X -> real_line_metric R) -> (forall x, 0 <= g x) -> 0 < t ->
  continuous ((fun x => real_power (g x) t) : X -> real_line_metric R).
Proof.
move=> hg hg0 ht x0; apply/cvg_ballP=> e he.
have [d hd hb] := real_power_local_bound (hg0 x0) ht he.
have hn := @cvg_ball _ (real_line_metric R) X (nbhs x0) (nbhs_filter x0) g (g x0) (hg x0) d hd.
apply: (@filterS X (nbhs x0) (nbhs_filter x0) _ _ _ hn)=> x.
rewrite /= !real_line_ball_distance /= => hx.
exact: hb (hg0 x) hx.
Qed.

End RealPowerContinuity.
