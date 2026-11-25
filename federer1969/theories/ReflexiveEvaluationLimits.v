(** Federer (1969), 2.9.22, p. 167: scalar derivative values define an
    element of Y** of norm at most Lip(g); reflexivity represents it by a
    unique vector v(x) in Y. This file proves that pointwise step through
    the abstract dual and bidual laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals.
From Federer Require Import Hom RealNormUP ContinuousRealFunctional RealFunctionalNormUP
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP ContinuousBidualIsometry
  RealCurveDerivativeUP RealCurveDerivativeLaws RealDerivativeOrder PuncturedRealLinearLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reflexive_bounded_evaluation_limits]: direct
    pointwise bidual step of Federer 2.9.22, p. 167. A
    norm-bounded vector family with scalar limits for every
    continuous linear functional has those limits represented by
    a vector of the same bound in a reflexive space. This is
    a weak-limit assertion; norm convergence is proved separately
    in Federer's subsequent integral/Lebesgue-point argument. *)
Theorem reflexive_bounded_evaluation_limits (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (u : R -> E) (L : R) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  0<=L -> (forall h, h!=0 -> N (u h)<=L) ->
  (forall a, exists l, punctured_real_limit (fun h => ed a (u h)) l) ->
  exists v : E, N v<=L /\
    forall a, punctured_real_limit (fun h => ed a (u h)) (ed a v).
Proof.
move=> ht hr hL hu hlim.
have [l hl] := choice hlim.
have hlin : linear (fun a : D => (l a : R^o)).
  move=> c a b; change (l (c *: a+b) = c * l a+l b).
  apply: (punctured_real_limit_unique (hl (c *: a+b))).
  have hsum := punctured_real_limit_add (punctured_real_limit_scale c (hl a)) (hl b).
  apply: (@punctured_real_limit_congr R
    (fun h => c * ed a (u h)+ed b (u h)))=> // h _.
  rewrite linearP.
  change (c * ed a (u h)+ed b (u h) = (c *: ed a+ed b) (u h)).
  by rewrite hom_addE hom_scaleE.
pose f := @HomMap R D R^o (fun a => l a) (introT (asboolP _) hlin).
have hbound a : `|l a|<=L * DN a.
  have hDa : 0<=DN a := real_functional_norm_nonnegative (continuous_dual_norm_laws hD a).
  apply: (@punctured_real_limit_order R (fun h => `|ed a (u h)|)
    (fun _ => L * DN a) `|l a| (L * DN a)
    (punctured_real_limit_absolute (hl a))
    (punctured_real_constant_limit (L * DN a)))=> h hn.
  have hh := real_functional_norm_bound (continuous_dual_norm_laws hD a) (u h).
  change (is_true (`|ed a (u h)|<=DN a * N (u h))) in hh.
  apply: le_trans hh _.
  have hmul := ler_wpM2l hDa (hu h hn).
  by rewrite [X in _<=X]mulrC in hmul.
have hc : is_continuous_real_functional (continuous_dual_norm_is_norm hD) (hom_as_linear f).
  apply: (@bounded_real_functional_continuous R D DN
    (continuous_dual_norm_is_norm hD) (hom_as_linear f) L hL).
  move=> a; exact: hbound.
have [b hb] := continuous_dual_surjective hB hc.
have hbn : BN b<=L.
  apply: (real_functional_norm_least (continuous_dual_norm_laws hB b) hL).
  move=> a; rewrite hom_as_linearE hb; exact: hbound.
have [v hv] := hr b.
exists v; split.
  by rewrite -(continuous_bidual_isometry hB ht v) hv.
move=> a.
have he : ed a v = l a.
  by rewrite -(ht v a) hv hb.
by rewrite he; exact: hl.
Qed.
