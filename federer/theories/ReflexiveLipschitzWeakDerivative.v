(** Federer (1969), 2.9.22, p. 167: the first half of the Lipschitz proof,
    through existence of v(x) representing every scalar derivative. A
    countable norm-dense subset of Y* is supplied explicitly at this stage;
    removing this hypothesis by the printed separability reduction and
    proving the norm derivative remain separate tasks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground RealFunctionalNormUP
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP
  MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure
  RealCurveDerivativeUP DenseDualEvaluationLimits ReflexiveEvaluationLimits
  LipschitzDualScalarisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_weak_normed_curve_derivative]: supporting
    dual-evaluation condition (v(x),alpha)=(alpha o g)'(x) in
    Federer 2.9.22, p. 167. This predicate records weak
    differentiability and is distinct from the book's required
    norm derivative, which needs the subsequent argument. *)
Definition is_weak_normed_curve_derivative (R : realType) (E D : lmodType R)
    (ed : Hom D (Hom E R^o)) (g : R -> E) (x : R) (v : E) :=
  forall a, has_real_curve_derivative (fun t => ed a (g t)) x (ed a v).

(** Source for [reflexive_lipschitz_weak_derivative_ae]: the
    common conull set and reflexive representation of v(x),
    Federer 2.9.22, p. 167, ending at the display |v(x)|<=Lip(g).
    This supporting theorem assumes a countable norm-dense dual
    set and proves the simultaneous assertion for all functionals.
    It does not claim to complete the strong derivative theorem. *)
Theorem reflexive_lipschitz_weak_derivative_ae (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R)
    (F : set (real_norm_metric_space (continuous_dual_norm_is_norm hD))) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  countable F -> dense F -> 0<=L ->
  (forall t u, N (g t-g u)<=L * `|t-u|) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, N v<=L /\ is_weak_normed_curve_derivative ed g x v].
Proof.
move=> ht hr hFc hFd hL hg.
have hc := @lipschitz_dual_derivatives_common_ae R E D N hN ed DN hD g L F hFc hg.
apply: (@measure_almost_everywhere_mono R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hc).
move=> x hx.
pose u h := h^-1 *: (g (x+h)-g x).
have hu h : h!=0 -> N (u h)<=L.
  exact: (@normed_lipschitz_difference_quotient_bound R E N hN g L x hg h).
have hFlim a : F a -> exists l, punctured_real_limit (fun h => ed a (u h)) l.
  move=> ha; have [v hv] := hx a ha; exists v.
  have heq : (fun h => ed a (u h)) =
      (fun h => (ed a (g (x+h))-ed a (g x))/h).
    apply/funext=> h; rewrite /u linearZ linearB.
    change (h^-1 * (ed a (g (x+h))-ed a (g x))=
      (ed a (g (x+h))-ed a (g x))/h).
    by rewrite mulrC.
  by rewrite heq.
have hall := @dense_dual_evaluation_limits R E D N hN ed DN hD F u L hFd hL hu hFlim.
have [v [hv hlim]] := @reflexive_bounded_evaluation_limits R E D B N hN
  ed DN hD eb BN hB tau u L ht hr hL hu hall.
exists v; split=> // a.
have heq : (fun h => ed a (u h)) =
    (fun h => (ed a (g (x+h))-ed a (g x))/h).
  apply/funext=> h; rewrite /u linearZ linearB.
  change (h^-1 * (ed a (g (x+h))-ed a (g x))=
    (ed a (g (x+h))-ed a (g x))/h).
  by rewrite mulrC.
have ha := hlim a; by rewrite heq in ha.
Qed.
