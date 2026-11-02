(** Federer (1969), 2.5.12, printed p. 105: the class G of represented
    members of Q contains f times y for f in L+ and y in D, and is closed
    under finite linear combinations. These are consequences of scalar
    representation and integral linearity. The local erratum has no
    correction to p. 105. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP FunctionLatticeUP RealIntegralFunctionalUP
  FunctionLatticeRegularityUP CountablyMeasurableUP VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellDualDensity
  VectorDaniellWeakMeasurability VectorDaniellPairingMeasurability
  MeasurableDualPairing VectorDaniellPairingConclusion VectorDaniellDensities
  VectorDaniellVariationIntegral MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  SummableRealArithmetic MeasureAlmostUP MeasureAlmostBasic LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Elementary.
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
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi (positive_function_lattice L)
  (variation_integral N Q T).
Hypothesis hreg : is_function_lattice_regular (positive_function_lattice L) phi.
Hypothesis hX : measure_countably_measurable phi setT.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_component_density_family N L T phi kk.
Local Notation k := (vector_density N D kk).
Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

(** Source for [vector_density_represents]: the class G in
    Federer 2.5.12, p. 105, consists of w in Q for which the
    pairing has the finite integral T(w). *)
Definition vector_density_represents (w : X -> E) :=
  Q w /\ is_measure_integral phi
    (real_total_integrand (fun x => k x (w x))) (T w)%:E.

(** Source for [vector_density_represents_elementary]: the first
    assertion about G in Federer 2.5.12, p. 105: f times y is
    represented when f belongs to L+ and y belongs to D. *)
Lemma vector_density_represents_elementary (f : X -> R) (y : E) :
  Lp f -> D y -> vector_density_represents (fun x => f x *: y).
Proof.
move=> hf hy; split; first exact (@vector_lattice_module_product R X E N hN L Q hM f y hf.1).
have hi := (hkk y).1.2 f hf.
apply: (measure_integral_almost_equal hphi hi).
apply: (measure_almost_everywhere_mono hphi _
  (vector_density_component_ae hL hQ hM hT hphi hrep hreg hX hD hkk hy))=> x hx.
exists (f x * kk y x)%:E; split; first by apply/real_total_integrand_graph.
apply/real_total_integrand_graph.
by rewrite (dual_space_scale _ _ (vector_density_dual hD kk x)) hx.
Qed.

(** Source for [vector_density_represents_zero]: zero belongs
    to the class G in Federer 2.5.12, p. 105, including
    the empty finite sum in the approximation argument. *)
Lemma vector_density_represents_zero :
  vector_density_represents (fun _ => 0).
Proof.
split; first exact: vector_function_space_zero hQ.
rewrite (variation_zero_map hQ hT).
have he : (fun x => k x 0)=(fun _ : X => 0).
  apply: funext=> x; exact: dual_space_zero (vector_density_dual hD kk x).
rewrite he; exact: real_total_zero_integral hphi.
Qed.

(** Source for [vector_density_represents_add]: closure of G
    under addition, used for eta = sum h_i times y_i in
    Federer 2.5.12, p. 105. *)
Lemma vector_density_represents_add (u v : X -> E) :
  vector_density_represents u -> vector_density_represents v ->
  vector_density_represents (fun x => u x+v x).
Proof.
move=> [hu hiu] [hv hiv]; split.
  exact (@vector_function_space_add R X E Q hQ u v hu hv).
rewrite (vector_variation_additive hT hu hv).
have he : (fun x => k x (u x+v x))=(fun x => k x (u x)+k x (v x)).
  apply: funext=> x; exact: dual_space_add _ _ (vector_density_dual hD kk x).
rewrite he; exact (@real_total_integral_add R X phi hphi _ _ (T u) (T v) hiu hiv).
Qed.

(** Source for [vector_density_represents_scale]: closure of G
    under real scalar multiplication, supporting the finite
    linear combinations in Federer 2.5.12, p. 105. *)
Lemma vector_density_represents_scale (c : R) (u : X -> E) :
  vector_density_represents u ->
  vector_density_represents (fun x => c *: u x).
Proof.
move=> [hu hi]; split.
  exact (@vector_function_space_scale R X E Q hQ c u hu).
rewrite (vector_variation_homogeneous hT c hu).
have he : (fun x => k x (c *: u x))=(fun x => c*k x (u x)).
  apply: funext=> x; exact: dual_space_scale _ _ (vector_density_dual hD kk x).
rewrite he; exact (@real_total_integral_scale R X phi hphi _ (T u) c hi).
Qed.

(** Source for [vector_density_represents_finite_sum]: the
    finite sum eta used in Federer 2.5.12, p. 105, belongs
    to G whenever each summand belongs to G. *)
Lemma vector_density_represents_finite_sum (J : eqType) (s : seq J)
    (u : J -> X -> E) :
  (forall j, j \in s -> vector_density_represents (u j)) ->
  vector_density_represents (fun x => \sum_(j <- s) u j x).
Proof.
elim: s=> [|j s ih] hu.
- have he : (fun x : X => \sum_(j <- [::]) u j x)=(fun _ : X => 0).
    by apply: funext=> x; rewrite big_nil.
  rewrite he; exact: vector_density_represents_zero.
- have he : (fun x => \sum_(i <- j::s) u i x)=
      (fun x => u j x+\sum_(i <- s) u i x) by apply: funext=> x; rewrite big_cons.
  rewrite he; apply: vector_density_represents_add.
  + apply: hu; by rewrite in_cons eqxx.
  + apply: ih=> i hi; apply: hu; by rewrite in_cons hi orbT.
Qed.
End Elementary.
