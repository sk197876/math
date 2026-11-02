(** Federer (1969), 2.5.14, p. 108: the actual integral formula for every
    member of Q, without the unit-series hypothesis. The G=Q argument of
    2.5.12, pp. 105–106, uses the proved Radon compact approximation in
    place of global lattice regularity, and compact supports turn local
    component agreement into ordinary almost agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology ring lra.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP FunctionLatticeUP RealIntegralFunctionalUP
  FunctionLatticeRegularityUP CountablyMeasurableUP VectorDaniellHypotheses
  VectorDaniellRationalSpan VectorDaniellDualExtension VectorDaniellDualDensity
  VectorDaniellPairingMeasurability VectorDaniellPairingConclusion
  VectorDaniellVariationIntegral VectorDaniellElementaryRepresentation
  SeparableVectorLone MeasureLpMembershipUP MeasurableNormedFunctionUP
  SummableRealArithmetic MeasureIntegralUniqueness CharacteristicVectorLoneDensity RadonCompactCharacteristicApproximation
  VectorLoneApproximation VectorDaniellIntegralFormula RadonMeasureUP BoundedComponentFamilyUP
  CompactSupportFunctionUP CompactSupportFunctionLattice RadonVectorDensityMeasurability RadonVectorElementary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Formula.
Variable R : realType.
Variable X : topologicalType.
Variable E : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Local Notation L := (@compactly_supported_continuous_functions R X).
Variable Q : set (X -> E).
Variable T : (X -> E) -> R.
(** Source for [hL]: K(X) lattice laws of Federer 2.5.13, p. 106,
    supporting the vector extension in 2.5.14, p. 108. *)
Let hL := @compactly_supported_continuous_functions_lattice R X.
Hypothesis hQ : is_vector_function_space Q.
Hypothesis hM : is_vector_lattice_module hN L Q.
Hypothesis hT : is_vector_variation_functional N L Q T.
Variable phi : set X -> \bar R.
Hypothesis hphi : is_measure phi.
Hypothesis hrep : is_real_integral_functional phi (positive_function_lattice L)
  (variation_integral N Q T).
Hypothesis hr : is_radon_measure phi.
Variable D : set E.
Hypothesis hD : is_rational_dense_subspace hN D.
Variable kk : E -> X -> R.
Hypothesis hkk : is_bounded_component_density_family N L T phi kk.
Local Notation k := (vector_density N D kk).
Local Notation Lp := (positive_function_lattice L).
Local Notation lam := (variation_integral N Q T).

(** Source for [radon_vector_density_integral_formula]: the Radon representation formula of Federer 2.5.14, p. 108,
    inherited from 2.5.12, p. 103,
    established by G = Q on pp. 105–106. The proof
    derives arbitrarily small errors from scalar lattice density;
    the integral formula is not an assumed representation law. *)
Theorem radon_vector_density_integral_formula (w : X -> E) : Q w ->
  is_measure_integral phi (real_total_integrand (fun x => k x (w x))) (T w)%:E.
Proof.
move=> hw.
have hmember v (hv : Q v) := @vector_member_lone R X E N hN L Q T hL hM phi hphi hrep D hD v hv.
have hwl := hmember w hw.
have hnorm : Lp (fun x => N (w x)).
  split; first exact (@vector_lattice_module_norm R X E N hN L Q hM w hw).
  move=> x; exact (real_seminorm_nonnegative hN.1 (w x)).
have [c [hc hcb]] := @radon_vector_density_pairing_summable R X E N hN Q T hQ hM hT
  phi hphi hr hrep D hD kk hkk w (lam (fun x => N (w x)))
  hwl.2.1.1 (hrep hnorm).
pose G := vector_density_represents N Q T phi D kk.
have hG0 : G (fun _ => 0).
  exact (@vector_density_represents_zero R X E N hN L Q T hQ hT phi hphi D hD kk).
have hGadd u v : G u -> G v -> G (fun x => u x+v x).
  exact (@vector_density_represents_add R X E N hN L Q T hQ hT phi hphi D hD kk u v).
have hGA u : G u -> is_measurable_normed_function phi
    (partial_function_total (u : X -> real_norm_metric_space hN)).
  move=> hu; exact: (hmember u hu.1).2.1.
have hGe f y : Lp f -> D y -> G (fun x => f x *: y).
  exact (@radon_vector_density_represents_elementary R X E N hN Q T hQ hM hT
    phi hphi hr hrep D hD kk hkk f y).
have ha := @characteristic_vector_lone_density R X E N hN phi hphi L
  (@radon_compact_characteristic_approximable R X phi hphi hr lam hrep)
  D hD G hG0 hGadd hGA hGe w hwl.
have hz : `|T w-c| = 0.
  apply/eqP; rewrite eq_le normr_ge0 andbT leNgt; apply/negP=> hpos.
  have he : 0 < `|T w-c|/4 by rewrite divr_gt0 // ltr0n.
  have [v [a [hv [hia hae]]]] := ha _ he.
  pose d x := w x-v x.
  have hnv := @vector_function_space_scale R X E Q hQ (-1) v hv.1.
  have hdQ : Q d.
    have hh := @vector_function_space_add R X E Q hQ w _ hw hnv.
    have heq : (fun x => w x+ -1 *: v x)=d.
      by apply: funext=> x; rewrite scaleN1r.
    by rewrite heq in hh.
  have hNd : Lp (fun x => N (d x)).
    split; first exact (@vector_lattice_module_norm R X E N hN L Q hM d hdQ).
    move=> x; exact (real_seminorm_nonnegative hN.1 (d x)).
  have hNa : lam (fun x => N (d x))=a.
    exact: EFin_inj (measure_integral_unique (hrep hNd) hia).
  have hTd : T d=T w-T v.
    have heq : d=(fun x => w x+ -1 *: v x).
      by apply: funext=> x; rewrite scaleN1r.
    rewrite heq (vector_variation_additive hT hw hnv)
      (vector_variation_homogeneous hT _ hv.1) mulN1r; by [].
  have hTb : `|T w-T v| <= a.
    rewrite -hTd -hNa; apply: (@variation_integral_absolute_bound R X E N hN L Q T hQ hT d _ hdQ hNd)=> x.
    exact: lexx.
  have hiDiff := @real_total_integral_subtract R X phi hphi
    (fun x => k x (w x)) (fun x => k x (v x)) c (T v) hc hv.2.
  have hpair : (fun x => k x (d x))=(fun x => k x (w x)-k x (v x)).
    apply: funext=> x; exact: dual_space_sub _ _ (vector_density_dual hD kk x).
  have [b [hbi hba]] := @radon_vector_density_pairing_summable R X E N hN Q T hQ hM hT
    phi hphi hr hrep D hD kk hkk d a (hmember d hdQ).2.1.1 hia.
  rewrite hpair in hbi.
  have hb : b=c-T v := EFin_inj (measure_integral_unique hbi hiDiff).
  rewrite hb in hba.
  have htriangle : `|T w-c| <= `|T w-T v|+`|c-T v|.
    have heq : T w-c=(T w-T v)-(c-T v) by ring.
    rewrite heq; have hh := ler_normD (T w-T v) (-(c-T v)).
    by rewrite normrN in hh.
  have hbound := le_trans htriangle (lerD hTb hba).
  have hlt := ltrD hae hae.
  have hfour : `|T w-c|/4+`|T w-c|/4 < `|T w-c|.
    lra.
  have hh := le_lt_trans hbound (lt_trans hlt hfour).
  by rewrite ltxx in hh.
have heq : T w=c by apply/eqP; rewrite -subr_eq0 -normr_eq0 hz eqxx.
by rewrite heq.
Qed.
End Formula.
