(** Federer (1969), 2.9.22, p. 167: approximate an arbitrary alpha in Y* by
    beta in a norm-dense set F, and apply Cauchy's criterion to the bounded
    difference quotients. The argument below isolates exactly that estimate.
    it does not state the reflexive-Banach extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric RealFunctionalNormUP
  ContinuousDualUP ContinuousDualNorm SeparableClosedCover
  RealCurveDerivativeUP PuncturedRealCauchy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_dual_evaluation_limits]: direct supporting
    estimate in the Lipschitz case of Federer 2.9.22, p. 167,
    from the choice of beta through Cauchy's criterion. A bounded
    vector family whose evaluations converge on a norm-dense set
    has convergent evaluations on the entire continuous dual.
    This proves scalar limits only; no norm limit is inferred here. *)
Theorem dense_dual_evaluation_limits (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (F : set (real_norm_metric_space (continuous_dual_norm_is_norm hD)))
    (u : R -> E) (L : R) :
  dense F -> 0<=L -> (forall h, h!=0 -> N (u h)<=L) ->
  (forall b, F b -> exists l, punctured_real_limit (fun h => ed b (u h)) l) ->
  forall a, exists l, punctured_real_limit (fun h => ed a (u h)) l.
Proof.
move=> hF hL hu hlim a; apply: punctured_real_cauchy_limit=> e he.
have hL1 : 0<L+1 by lra.
have he6 : 0<e/6 by rewrite divr_gt0 // ltr0n.
have hr : 0<(e/6)/(L+1) by rewrite divr_gt0.
have [b [hb hnear]] := metric_dense_point_near hF a hr.
change (is_true (DN (a-b)<(e/6)/(L+1))) in hnear.
have hsmall : DN (a-b)*(L+1)<e/6.
  by move: hnear; rewrite ltr_pdivlMr.
have hDb : 0<=DN (a-b) :=
  real_functional_norm_nonnegative (continuous_dual_norm_laws hD (a-b)).
have heval y : ed (a-b) y=ed a y-ed b y.
  rewrite linearB; by [].
have happrox h : h!=0 -> `|ed a (u h)-ed b (u h)|<e/6.
  move=> hn; rewrite -heval.
  have hB := real_functional_norm_bound (continuous_dual_norm_laws hD (a-b)) (u h).
  change (is_true (`|ed (a-b) (u h)|<=DN (a-b)*N (u h))) in hB.
  have hB' := le_trans hB (ler_wpM2l hDb (hu h hn)).
  apply: le_lt_trans hB' _; apply: le_lt_trans _ hsmall.
  by rewrite mulrDr mulr1 lerDl.
have [l hl] := hlim b hb.
have [d [hd hB]] := hl (e/6) he6.
exists d; split=> // h k hh hk.
have hn : h!=0 by move: hh=> /andP [h0 _]; move: h0; rewrite normr_gt0.
have kn : k!=0 by move: hk=> /andP [k0 _]; move: k0; rewrite normr_gt0.
have h1 := happrox h hn; have h2 := hB h hh.
have h3 : `|l-ed b (u k)|<e/6 by rewrite distrC; exact: hB k hk.
have h4 : `|ed b (u k)-ed a (u k)|<e/6 by rewrite distrC; exact: happrox k kn.
have t1 := ler_distD (ed b (u h)) (ed a (u h)) (ed a (u k)).
have t2 := ler_distD l (ed b (u h)) (ed a (u k)).
have t3 := ler_distD (ed b (u k)) l (ed a (u k)).
by lra.
Qed.
