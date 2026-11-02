(** Federer (1969), 2.5.12, printed pp. 105–106: proof that G = Q and hence
    T(w) = integral <w,k>. We use finite sums h_i y_i and the scalar lattice
    density as in the book. Global L1 approximation replaces the printed
    finite-support reduction followed by truncation. *)
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
  SummableRealArithmetic MeasureIntegralUniqueness DaniellVectorLoneDensity
  VectorLoneApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Formula.
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

(** Source for [vector_member_lone]: the measurability and
    summability of nu o w used in Federer 2.5.12, p. 105.
    The former was proved on p. 104; the latter follows
    from nu o w in L+ and the representing measure. *)
Lemma vector_member_lone (w : X -> E) : Q w ->
  is_measure_lp_function phi 1
    (partial_function_total (w : X -> real_norm_metric_space hN)).
Proof.
move=> hw.
have hnorm : Lp (fun x => N (w x)).
  split; first exact (@vector_lattice_module_norm R X E N hN L Q hM w hw).
  move=> x; exact (real_seminorm_nonnegative hN.1 (w x)).
have hm := @vector_member_measurable R X E N hN L Q T hL hM phi hphi hrep D hD w hw.
exact (@separable_vector_summable_norm_lone R X E N hN D hD phi hphi w
  (lam (fun x => N (w x))) hm (hrep hnorm)).
Qed.

(** Source for [variation_integral_absolute_bound]: the bound
    |T(w)| <= lambda(nu o w) used in the last estimate
    on p. 105 of Federer 2.5.12. We state the more
    general admissible positive majorant f, directly from
    the supremum definition and linearity at -w. *)
Lemma variation_integral_absolute_bound (w : X -> E) (f : X -> R) :
  Q w -> Lp f -> function_le (fun x => N (w x)) f ->
  `|T w| <= lam f.
Proof.
move=> hw hf hb.
have hp := @variation_integral_upper R X E N hN L Q T hQ hT f w hf hw hb.
have hnw := @vector_function_space_scale R X E Q hQ (-1) w hw.
have hn : T (fun x => -1 *: w x) <= lam f.
  apply: (@variation_integral_upper R X E N hN L Q T hQ hT f _ hf hnw)=> x.
  rewrite (real_seminorm_scale hN.1) normrN1 mul1r; exact: hb.
rewrite (vector_variation_homogeneous hT _ hw) mulN1r in hn.
rewrite ler_norml; apply/andP; split; first by rewrite lerNl.
exact: hp.
Qed.

(** Source for [vector_density_integral_formula]: the displayed
    representation formula of Federer 2.5.12, p. 103,
    established by G = Q on pp. 105–106. The proof
    derives arbitrarily small errors from scalar lattice density;
    the integral formula is not an assumed representation law. *)
Theorem vector_density_integral_formula (w : X -> E) : Q w ->
  is_measure_integral phi (real_total_integrand (fun x => k x (w x))) (T w)%:E.
Proof.
move=> hw.
have hwl := vector_member_lone hw.
have hnorm : Lp (fun x => N (w x)).
  split; first exact (@vector_lattice_module_norm R X E N hN L Q hM w hw).
  move=> x; exact (real_seminorm_nonnegative hN.1 (w x)).
have [c [hc hcb]] := @vector_density_pairing_summable R X E N hN L Q T hL hQ hM hT
  phi hphi hrep hreg hX D hD kk hkk w (lam (fun x => N (w x)))
  hwl.2.1.1 (hrep hnorm).
pose G := vector_density_represents N Q T phi D kk.
have hG0 : G (fun _ => 0).
  exact (@vector_density_represents_zero R X E N hN L Q T hQ hT phi hphi D hD kk).
have hGadd u v : G u -> G v -> G (fun x => u x+v x).
  exact (@vector_density_represents_add R X E N hN L Q T hQ hT phi hphi D hD kk u v).
have hGA u : G u -> is_measurable_normed_function phi
    (partial_function_total (u : X -> real_norm_metric_space hN)).
  move=> hu; exact: (vector_member_lone hu.1).2.1.
have hGe f y : Lp f -> D y -> G (fun x => f x *: y).
  exact (@vector_density_represents_elementary R X E N hN L Q T hL hQ hM hT
    phi hphi hrep hreg hX D hD kk hkk f y).
have ha := @daniell_vector_lone_density R X E N hN phi hphi L lam hL hrep hreg
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
    rewrite -hTd -hNa; apply: variation_integral_absolute_bound hdQ hNd _=> x.
    exact: lexx.
  have hiDiff := @real_total_integral_subtract R X phi hphi
    (fun x => k x (w x)) (fun x => k x (v x)) c (T v) hc hv.2.
  have hpair : (fun x => k x (d x))=(fun x => k x (w x)-k x (v x)).
    apply: funext=> x; exact: dual_space_sub _ _ (vector_density_dual hD kk x).
  have [b [hbi hba]] := @vector_density_pairing_summable R X E N hN L Q T hL hQ hM hT
    phi hphi hrep hreg hX D hD kk hkk d a (vector_member_lone hdQ).2.1.1 hia.
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
