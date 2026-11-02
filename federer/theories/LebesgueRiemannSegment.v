(** Supporting elementary integral identification for Federer (1969),
    2.6.3(2), pp. 117–118, through the interval identity in 2.5.17, p. 111. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderLimit ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension SummableRealFunctionUP
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeUP
  RealIntegralFunctionalUP CurveVariationUP CurveArcLength StieltjesSums StieltjesIntegral
  StieltjesDaniellIntegral StieltjesMonotone StieltjesSegmentIdentity
  StieltjesContinuityPoints IntervalBumpFunctions LebesgueScalarMeasure LebesgueRiemannFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_riemann_compact_segment]: the
    interval identity of Federer 2.5.17, p. 111,
    specialised to g(x)=x, supporting 2.6.3(2),
    pp. 117–118. The proof uses the existing bump
    approximation and bounded convergence, with the actual
    sealed L^1 measure. *)
Theorem lebesgue_riemann_compact_segment (R : realType) (F : R -> R) (a b : R) :
  compactly_supported_continuous_functions F -> a < b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand F) (stieltjes_integral (fun x => x) F a b)%:E.
Proof.
move=> hF hab.
have hm := lebesgue_scalar_is_measure R.
have hi := @lebesgue_scalar_riemann_functional R.
have hip : is_real_integral_functional (@lebesgue_scalar_measure R)
    (positive_function_lattice (@compactly_supported_continuous_functions R R))
    (induced_daniell (fun x : R => x)) by move=> f [hf _]; exact: hi.
have [c [l [hc [hl hlim]]]] := bump_measure_limit a b hm hip hF.
have hg : curve_locally_finite_variation ((fun x : R => x) : R -> real_line_metric R).
  apply: monotone_locally_finite_variation; by move=> x y h.
have he : forall n, stieltjes_integral (fun x => x)
    (fun x => interval_bump a b n x*F x) a b = c n.
  move=> n; have hprod := KR_product (interval_bump_member a b n) hF.
  have hh := measure_integral_unique (hi _ hprod) (hc n).
  have hz : forall x, interval_bump a b n x*F x <> 0 -> a < x < b.
    move=> x hx; apply: (interval_bump_support (n:=n))=> h0; apply: hx; by rewrite h0 mul0r.
  have hv := induced_daniell_value hg hprod (ltW hab) hz.
  rewrite -hv; by injection hh.
have hvalue : l = stieltjes_integral (fun x => x) F a b.
  apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
  apply/ler_addgt0Pr=> e hep; rewrite add0r.
  have he2 : 0 < e/2 by lra.
  have [N1 h1] := order_limit_real hlim he2.
  have [N2 h2] := @bump_product_integral_limit R (fun x => x) hg F a b (e/2)
    (KR_continuous hF) hab (cvg_id : (fun x : R => x) @ a --> a)
    (cvg_id : (fun x : R => x) @ b --> b) he2.
  pose n := maxn N1 N2.
  have h1' := h1 n (leq_maxl N1 N2).
  have h2' := h2 n (leq_maxr N1 N2); rewrite he in h2'.
  move: h1' h2'; rewrite !ltr_norml=> /andP[h11 h12] /andP[h21 h22].
  rewrite ler_norml; apply/andP; split; lra.
rewrite -hvalue.
exact: segment_subset_integral hm (lebesgue_scalar_singleton a) (lebesgue_scalar_singleton b) hl.
Qed.

(** Source for [continuous_segment_compact_extension]: supporting
    cutoff for the interval identity of Federer 2.5.17,
    p. 111, used in 2.6.3(2), pp. 117–118.
    Multiplication by the book's interval bump on the larger
    interval [a-1,b+1] preserves all values on [a,b]. *)
Lemma continuous_segment_compact_extension (R : realType) (F : R -> R) (a b : R) :
  continuous F -> exists G : R -> R,
    compactly_supported_continuous_functions G /\
    forall x, a <= x <= b -> G x=F x.
Proof.
move=> hF; pose h := interval_bump (a-1) (b+1) 0.
exists (fun x => h x*F x); split.
- have hh := interval_bump_member (a-1) (b+1) 0.
  split.
  + have hc : continuous h := KR_continuous hh.
    move=> x; exact: cvgM (hc x) (hF x).
  + apply: (@compact_support_unary_operation R R h _ hh.2)=> x ->; exact: mul0r.
- move=> x /andP[hax hxb]; rewrite /h interval_bump_inner_one ?mul1r //=; lra.
Qed.
