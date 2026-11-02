(** Federer (1969), 2.9.22, p. 168, last displayed quotient: the norm
    derivative of H o s is H'(s(x)) s'(x). This supporting chain rule is
    proved from first-order errors, without a calculus import. It also
    includes s'(x)=0 and increments where s(x+h)=s(x), avoiding division by
    that possibly zero difference. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP RealCurveDerivativeUP RealDerivativeIncrementBounds
  NormedCurveDerivativeUP NormedDerivativeRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_curve_derivative_compose]: direct local
    chain-rule implication at the end of Federer 2.9.22, p. 168.
    The proof gives a stronger zero-parameter-derivative case
    whenever H itself is norm differentiable. The book's separate
    zero case only assumes H Lipschitz and is covered by
    normed_curve_zero_derivative_from_control. No reflexivity
    hypothesis is needed once both derivatives exist. *)
Theorem normed_curve_derivative_compose (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (H : R -> E)
    (s : R -> R) (x w : R) v :
  has_real_curve_derivative s x w -> has_normed_curve_derivative N H (s x) v ->
  has_normed_curve_derivative N (fun t => H (s t)) x (w *: v).
Proof.
move=> hs hH; apply: (normed_derivative_from_displacement_error hN)=> e he.
pose K := `|w|+1.
pose Q := N v+1.
have hw0 := normr_ge0 w; have hv0 := real_seminorm_nonnegative hN.1 v.
have hK : 0<K by rewrite /K; lra.
have hQ : 0<Q by rewrite /Q; lra.
have heH : 0<e/(2*K) by rewrite divr_gt0 // mulr_gt0 // ltr0n.
have heS : 0<e/(2*Q) by rewrite divr_gt0 // mulr_gt0 // ltr0n.
have [dH [hdH hHB]] := normed_derivative_small_displacement_error hN hH heH.
have [d1 [hd1 hS1]] := real_derivative_small_displacement_error hs (@ltr01 R).
have [dS [hdS hSB]] := real_derivative_small_displacement_error hs heS.
have hdHK : 0<dH/K by rewrite divr_gt0.
exists (Num.min d1 (Num.min dS (dH/K))); split.
  by rewrite !lt_min hd1 hdS hdHK.
move=> h hsmall.
have hd' : `|h|<d1 /\ `|h|<dS /\ `|h|<dH/K.
  by move: hsmall; rewrite !lt_min=> /andP [h1 /andP [h2 h3]]; split=> //; split.
pose k := s (x+h)-s x.
have hks : `|k|<=K * `|h|.
  have herr := hS1 h hd'.1; rewrite mul1r in herr.
  have ht := ler_distD (w*h) (s (x+h)-s x) 0.
  rewrite !subr0 normrM in ht.
  change (is_true (`|k-w*h|<=`|h|)) in herr.
  have heq : K * `|h|=`|w| * `|h|+`|h| by rewrite /K mulrDl mul1r.
  by rewrite heq; rewrite /k in herr *; lra.
have hkH : `|k|<dH.
  have hm : K * `|h|<dH.
    by move: hd'.2.2; rewrite ltr_pdivlMr // mulrC.
  exact: le_lt_trans hks hm.
have hHv := hHB k hkH.
have hSk := hSB h hd'.2.1.
change (is_true (`|k-w*h|<=e/(2*Q) * `|h|)) in hSk.
have hHbound : N (H (s x+k)-H (s x)-k *: v)<=e/2 * `|h|.
  have hh := ler_wpM2l (ltW heH) hks.
  have hid : e/(2*K) * (K * `|h|)=e/2 * `|h|.
    by field; rewrite (gt_eqF hK).
  rewrite hid in hh; exact: le_trans hHv hh.
have hcoeff : e/(2*Q) * N v<=e/2.
  have hvQ : N v<=Q by rewrite /Q; lra.
  have hh := ler_wpM2l (ltW heS) hvQ.
  have hid : e/(2*Q) * Q=e/2 by field; rewrite (gt_eqF hQ).
  by rewrite hid in hh.
have hSbound : N ((k-w*h) *: v)<=e/2 * `|h|.
  rewrite (real_seminorm_scale hN.1).
  have hh := ler_wpM2r hv0 hSk.
  rewrite mulrAC in hh.
  exact: le_trans hh (ler_wpM2r (normr_ge0 h) hcoeff).
have hid : H (s (x+h))-H (s x)-h *: (w *: v)=
    (H (s x+k)-H (s x)-k *: v)+(k-w*h) *: v.
  have hk : s x+k=s (x+h) by rewrite /k addrC subrK.
  rewrite hk [(k-w*h) *: v]scalerBl addrA subrK !scalerA.
  by rewrite [w*h]mulrC.
rewrite hid.
have ht := real_seminorm_triangle hN.1
  (H (s x+k)-H (s x)-k *: v) ((k-w*h) *: v).
have hh := lerD hHbound hSbound.
have heq : e/2 * `|h|+e/2 * `|h|=e * `|h|.
  have he2 : e/2+e/2=e by lra.
  by rewrite -mulrDl he2.
by rewrite heq in hh; exact: le_trans ht hh.
Qed.
