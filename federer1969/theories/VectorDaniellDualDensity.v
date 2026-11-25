(** Federer (1969), 2.5.12, p. 104, third paragraph of the proof: for phi
    almost all x the map sending y in D into k_y(x) is Q linear and nu
    bounded, hence has a unique extension k(x) in U*. On the exceptional
    null set k(x) is the zero functional. The function k is obtained here
    from any choice of the densities k_y of 2.5.9 and any countable dense
    rational subspace D; it satisfies <y, k(x)> = k_y(x) for y in D and phi
    almost all x, and takes values in the weakly topologized space E*. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground FunctionLatticeUP
  MeasureUP RealIntegralFunctionalUP FunctionLatticeRegularityUP CountablyMeasurableUP
  MeasureAlmostUP MeasureAlmostBasic VectorDaniellHypotheses VectorDaniellRationalSpan
  VectorDaniellDualExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DualDensity.
Variable R : realType.
Variable X : choiceType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable L : set (X -> R).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
Hypothesis hL : is_function_lattice L.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.

Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi Lp lam.
Hypothesis hreg : is_function_lattice_regular Lp phi.
Hypothesis hX : measure_countably_measurable phi setT.

Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_component_density_family N L T phi kk.

(** Source for [density_good_set]: the set of points x at which the map
    sending y in D into k_y(x) is Q linear and nu bounded, Federer
    2.5.12, p. 104. *)
Definition density_good_set : set X :=
  [set x | forall (y z : E) (r s : rat), D y -> D z ->
    kk (ratr r *: y + ratr s *: z) x = ratr r * kk y x + ratr s * kk z x /\ `|kk y x| <= N y].

(** Source for [density_good_set_ae]: phi almost all points of X belong
    to the good set, Federer 2.5.12, p. 104. *)
Lemma density_good_set_ae : measure_almost_everywhere phi density_good_set.
Proof. exact (component_density_rational_linear hL hQ hM hT hphi hrep hreg hX hkk hD.1). Qed.

(** Source for [density_good_linear]: Q linearity of y -> k_y(x) on D at
    a good point, Federer 2.5.12, p. 104. *)
Lemma density_good_linear (x : X) : density_good_set x ->
  forall (r s : rat) (y z : E), D y -> D z ->
    kk (ratr r *: y + ratr s *: z) x = ratr r * kk y x + ratr s * kk z x.
Proof. by move=> h r s y z hy hz; exact: (h y z r s hy hz).1. Qed.

(** Source for [density_good_bound]: the bound |k_y(x)| <= nu(y) on D at
    a good point, Federer 2.5.12, p. 104. *)
Lemma density_good_bound (x : X) : density_good_set x -> forall y, D y -> `|kk y x| <= N y.
Proof. by move=> h y hy; exact: (h y y 0 0 hy hy).2. Qed.

(** Source for [vector_density]: the function k of Federer 2.5.12,
    p. 104: at a good point x, k(x) is the unique extension in U* of the
    map sending y in D into k_y(x); elsewhere k(x) = 0. *)
Definition vector_density (x : X) : E -> R :=
  if `[< density_good_set x >] then dual_extension N D (fun y => kk y x) else (fun _ => 0).

(** Source for [vector_density_unit_ball]: k takes values in U*,
    Federer 2.5.12, p. 104. *)
Lemma vector_density_unit_ball (x : X) : dual_unit_ball hN (vector_density x).
Proof.
rewrite /vector_density; case: asboolP => h.
  exact: (dual_extension_unit_ball hD (density_good_linear h) (density_good_bound h)).
exact: zero_dual_unit_ball.
Qed.

(** Source for [vector_density_dual]: k takes values in E*, Federer
    2.5.12, p. 104. *)
Lemma vector_density_dual (x : X) : dual_space hN (vector_density x).
Proof. exact: (vector_density_unit_ball x).1. Qed.

(** Source for [vector_density_bound]: the estimate
    |<v, k(x)>| <= nu(v), Federer 2.5.12, p. 104. *)
Lemma vector_density_bound (x : X) (v : E) : `|vector_density x v| <= N v.
Proof. by have /dual_unit_ball_bound [_ hb] := vector_density_unit_ball x; exact: hb. Qed.

(** Source for [vector_density_agree]: <y, k(x)> = k_y(x) for y in D at
    a good point x, Federer 2.5.12, p. 104. *)
Lemma vector_density_agree (x : X) (y : E) : density_good_set x -> D y -> vector_density x y = kk y x.
Proof.
move=> hx hy; rewrite /vector_density; case: asboolP => [_|hn]; last by case: hn.
exact: (dual_extension_agree hD (density_good_linear hx) (density_good_bound hx) hy).
Qed.

(** Source for [vector_density_component_ae]: <y, k> = k_y phi almost
    everywhere for y in D, Federer 2.5.12, p. 104. *)
Lemma vector_density_component_ae (y : E) : D y ->
  measure_almost_everywhere phi [set x | vector_density x y = kk y x].
Proof.
move=> hy; apply: (measure_almost_everywhere_mono hphi _ density_good_set_ae) => x hx.
exact: vector_density_agree.
Qed.

(** Source for [vector_density_point]: k(x) as a point of the weakly
    topologized space E*, Federer 2.5.12, p. 103. *)
Definition vector_density_point (x : X) : weak_dual_space hN :=
  @exist (weak_function_space E) (fun alpha => alpha \in (dual_space hN : set (weak_function_space E)))
    (vector_density x) (mem_set (vector_density_dual x)).

(** Source for [vector_density_pointE]: the functional underlying the
    point k(x) of E*, Federer 2.5.12, p. 103. *)
Lemma vector_density_pointE (x : X) : val (vector_density_point x) = vector_density x.
Proof. by []. Qed.

End DualDensity.
