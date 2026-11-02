(** Federer (1969), 2.7.16, printed p. 140, example (6): "We also define
    beta_oo(n, m) = 1. From 2.4.12 and 1.7.7 we see that, if xi in Lambda_m
    R^n, xi is simple and f(p) = |<xi, Lambda_m p>| for p in O*(n, m), then
    [theta*_{n,m}]_(t)(f) = beta_t(n, m) . |xi| whenever 1 <= t <= oo." Here
    <xi, Lambda_m p> = (Lambda_m p) xi, f is projection_norm
    (OrthogonalProjectionConstants.v), and [phi]_(t) is the seminorm of
    2.4.12, p. 86: for t < oo the specification is_measure_lp_norm, (int
    |f|^t dphi)^{1/t}, and for t = oo the essential norm
    is_measure_essential_norm, the infimum of the numbers r >= 0 with phi{p
    : |f(p)| > r} = 0. For finite t the assertion is the defining equation
    of beta_t(n, m). For t = oo Federer gives no argument beyond the
    references; it is supplied: |(Lambda_m p) xi| <= |xi| for every p
    (1.7.7, p. 34) shows that |xi| is admissible; if 0 <= r < |xi|, then u =
    max{f - r, 0} is a nonnegative member of K(O*(n, m)) with u(p_0) = |xi|
    - r > 0 for the p_0 of 1.7.7, so that the invariant integral of u is
    positive (InvariantIntegralPositivity.v) while u vanishes outside {p :
    f(p) > r}; hence this set does not have measure zero. The local erratum
    has no entry for p. 140. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology constructive_ereal.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import TensorUP InnerProductUP InnerNorm InnerMetric LinearBasis Hom HomInner AdjointUP
  Adjoint OrthogonalMaps
  OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  CoordinateProjection IsotropyGroupTopology TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  RealMetricBackground CompactSupportFunctionUP FunctionLatticeUP MonotoneDaniellIntegralUP
  CovariantIntegralUP HaarIntegralUP RealIntegralFunctionalUP SummableRealFunctionUP PartialFunctionUP
  PartialFunctionBasic PartialFunctionPostcomposition PartialNormPower MeasureUP MeasureBasic
  MeasureAlmostUP MeasureGauge MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureDensityNullSets
  MeasureLpNormUP MeasureEssentialNormUP MeasureEssentialNorm ExtendedPositivePower RealPower
  HomSpaceTopology LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure CompactGroupHomogeneousMeasures OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures InvariantIntegralPositivity ExteriorGrading ExteriorMaps
  ExteriorMapScaling FiniteExteriorPowers ExteriorNorm AssociatedSubspace SimpleElementary
  SimpleProjectionAttainment OrthogonalProjectionConstants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProjectionNorms.
Variable R : realType.
Hypothesis h2 : (1 + 1 : R) != 0.
Local Notation hBn j := (@euclidean_inner_productP R j).
Local Notation hbn j := (@coordinate_basisP R j).

(** Source for [is_extended_projection_constant]: "We also define
    beta_oo(n, m) = 1", Federer 2.7.16, p. 140, together with beta_t(n, m)
    for 1 <= t < oo of p. 139: the constant for an extended exponent t.
    Definition. *)
Definition is_extended_projection_constant (t : \bar R) (n m : nat) (beta : R) : Prop :=
  match t with
  | +oo%E => beta = 1
  | r%:E => is_projection_constant h2 r n m beta
  | -oo%E => False
  end.

(** Source for [projection_constant_infinity]: "We also define
    beta_oo(n, m) = 1", Federer 2.7.16, p. 140. Direct formalisation. *)
Lemma projection_constant_infinity n m : is_extended_projection_constant +oo%E n m 1.
Proof. by []. Qed.

Variables (n m : nat).
Local Notation OP := (set_type (euclidean_orthogonal_projections R n m)).
Variables (mulS : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n ->
    euclidean_orthogonal_group R n)
  (invS : euclidean_orthogonal_group R n -> euclidean_orthogonal_group R n)
  (eS : euclidean_orthogonal_group R n).
Hypothesis hS : is_subgroup_restriction (linear_group_mul (hBn n) (hbn n)) (linear_group_inv (hBn n) (hbn n))
  (linear_group_unit (hBn n) (hbn n)) (euclidean_orthogonal_group R n) mulS invS eS.
Local Notation A := (orthogonal_projection_action (hBn m) (hBn n) (hbn n) hS).

(** Source for [projection_norm_lp]: "[theta*_{n,m}]_(t)(f) =
    beta_t(n, m) . |xi|" for 1 <= t < oo, Federer 2.7.16, p. 140, with
    the seminorm of 2.4.12, p. 86. Direct formalisation: the
    specification is_measure_lp_norm holds with the value beta |xi|. *)
Theorem projection_norm_lp (t beta : R) (phi : set OP -> \bar R) (xi : exterior_power (R_n R n) m) :
  1 <= t -> is_projection_constant h2 t n m beta -> is_normalised_invariant_measure A phi -> simple xi ->
  is_measure_lp_norm phi (fun x : R => `|x|) t (partial_function_total (projection_norm h2 xi))
    (beta * exterior_norm h2 (hBn n) xi)%:E.
Proof.
move=> ht [hb hbeta] hphi hs; split=> //.
have [a ha hroot] := hbeta _ _ _ hS phi hphi xi hs.
exists a; split; last by rewrite hroot.
apply: (measure_integral_graph_equivalent _ ha)=> p y; split.
- move=> /real_total_integrand_graph <-; exists (projection_norm h2 xi p); split=> //.
  by rewrite ger0_norm ?projection_norm_nonnegative.
- move=> [z [hz <-]]; apply/real_total_integrand_graph.
  by rewrite -hz /= ger0_norm ?projection_norm_nonnegative.
Qed.

(** Source for [projection_norm_essential]: "[theta*_{n,m}]_(oo)(f) =
    beta_oo(n, m) . |xi|" with beta_oo(n, m) = 1, Federer 2.7.16,
    p. 140, from 2.4.12, p. 86, and 1.7.7, p. 34. Direct formalisation
    for every normalised invariant measure phi over O*(n, m); the proof
    is supplied (see the header). *)
Theorem projection_norm_essential (phi : set OP -> \bar R) (xi : exterior_power (R_n R n) m) :
  is_normalised_invariant_measure A phi -> simple xi ->
  is_measure_essential_norm phi (fun x : R => `|x|) (partial_function_total (projection_norm h2 xi))
    (exterior_norm h2 (hBn n) xi)%:E.
Proof.
move=> hphi hs.
have [nu [hnu hrep hm _]] := normalised_invariant_measure_integral hphi.
set f := projection_norm h2 xi.
have hf0 p : 0 <= f p := projection_norm_nonnegative h2 xi p.
have hsup r : partial_norm_superlevel (fun x : R => `|x|) (partial_function_total f) r =
    [set p | (r < (f p)%:E)%E].
  apply/seteqP; split=> p.
  - by move=> [y [hy hr]]; move: hr; rewrite /= -hy (ger0_norm (hf0 p)).
  - move=> hr; exists (f p); split=> //; by rewrite /= (ger0_norm (hf0 p)).
have hfeas : measure_essential_norm_feasible phi (fun x : R => `|x|) (partial_function_total f)
    (exterior_norm h2 (hBn n) xi)%:E.
  split; first by rewrite lee_fin exterior_norm_nonnegative.
  rewrite hsup.
  have -> : [set p | ((exterior_norm h2 (hBn n) xi)%:E < (f p)%:E)%E] = set0.
    apply/seteqP; split=> // p; rewrite /= lte_fin ltNge projection_norm_bound //.
  exact: measure_empty hm.
split; last by move=> b hb; exact: hb _ hfeas.
move=> r [hr0 hr]; case: r hr0 hr => [r'| |] hr0 hr //; last by rewrite leey.
rewrite lee_fin in hr0; rewrite lee_fin leNgt; apply/negP=> hlt.
have hx : xi != 0.
  apply/eqP=> hx0; move: hlt; rewrite hx0 exterior_norm_zero ltNge hr0.
  by [].
have [g [p [hg [hadj hp]]]] := simple_projection_norm_attained h2 (hBn n) hx hs.
have hpp : is_orthogonal_projection (@euclidean_inner_product R n) (@euclidean_inner_product R m) p.
  by exists g.
pose p0 : OP := orthogonal_projection_of (hBn m) (hBn n) (hbn n) hpp.
have hfp0 : f p0 = exterior_norm h2 (hBn n) xi.
  rewrite /f /projection_norm -hp; congr (exterior_norm _ _ _); apply: exterior_power_map_ext=> v.
  by rewrite hom_as_linearE; exact: hom_of_linearE.
pose u := (fun q => f q - r') \max (fun _ : OP => 0 : R^o).
have hfc : continuous (f : OP -> real_line_metric R) := projection_norm_continuous hs.
have huc : continuous (u : OP -> real_line_metric R).
  move=> q; apply: continuous_max; last exact: cst_continuous.
  exact: (@continuousB R R^o OP f (fun _ => r') q (hfc q) (@cst_continuous OP R^o r' q)).
have huK := projection_space_continuous_compact hS huc.
have hu0 q : 0 <= u q by rewrite /u le_max lexx orbT.
have hpos : 0 < nu u.
  apply: (nonzero_invariant_integral_positive
    (topological_group_laws (lch_group_topological (orthogonal_group_lch hS)))
    (orthogonal_projections_homogeneous (hBn m) (hbn m) hS) hnu huK hu0).
  exists p0; rewrite /u /= hfp0; apply/eqP; rewrite gt_eqF // lt_max subr_gt0 hlt.
  by [].
have hint := hrep _ huK.
have hzero : is_measure_integral phi (real_total_integrand u) 0%E.
  apply: (measure_integral_almost_equal hm (measure_extended_zero_integral hm)).
  rewrite /measure_almost_equal /measure_almost_everywhere.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: (@le_trans _ _ (phi (partial_norm_superlevel (fun x : R => `|x|) (partial_function_total f)
    r'%:E))); last by rewrite hr.
  rewrite hsup; apply: measure_mono=> // q hq; rewrite /= lte_fin.
  apply: contrapT=> hq'; apply: hq; exists 0%E; split=> //.
  apply/real_total_integrand_graph; congr (_%:E).
  rewrite /u /=; apply/eqP; rewrite eq_le hu0 andbT ge_max lexx andbT subr_le0.
  by rewrite leNgt; apply/negP.
have := measure_integral_unique hint hzero; case=> hnu0.
by move: hpos; rewrite hnu0 ltxx.
Qed.

(** Source for [projection_norm_essential_value]: the value of the
    essential norm, "[theta*_{n,m}]_(oo)(f) = beta_oo(n, m) . |xi|",
    Federer 2.7.16, p. 140, for the public phi_(oo) of 2.4.12, p. 86.
    Direct formalisation. *)
Corollary projection_norm_essential_value (phi : set OP -> \bar R) (xi : exterior_power (R_n R n) m) :
  is_normalised_invariant_measure A phi -> simple xi ->
  measure_essential_norm phi (fun x : R => `|x|) (partial_function_total (projection_norm h2 xi)) =
    (1 * exterior_norm h2 (hBn n) xi)%:E.
Proof.
move=> hphi hs; rewrite mul1r.
have [h1 h2'] := projection_norm_essential hphi hs.
have [s1 s2] := measure_essential_norm_specification phi (fun x : R => `|x|)
  (partial_function_total (projection_norm h2 xi)).
apply/eqP; rewrite eq_le; apply/andP; split; first exact: h2' _ s1.
exact: s2 _ h1.
Qed.

(** Source for [projection_norm_seminorm]: "if xi in Lambda_m R^n, xi
    is simple and f(p) = |<xi, Lambda_m p>| for p in O*(n, m), then
    [theta*_{n,m}]_(t)(f) = beta_t(n, m) . |xi| whenever 1 <= t <= oo",
    Federer 2.7.16, p. 140. Direct formalisation for an extended exponent
    t: the L_t seminorm specification of 2.4.12 for finite t, and the
    essential norm for t = oo, with beta = beta_t(n, m) given by
    is_extended_projection_constant. *)
Theorem projection_norm_seminorm (t : \bar R) (beta : R) (phi : set OP -> \bar R)
    (xi : exterior_power (R_n R n) m) :
  (1 <= t)%E -> is_extended_projection_constant t n m beta ->
  is_normalised_invariant_measure A phi -> simple xi ->
  match t with
  | r%:E => is_measure_lp_norm phi (fun x : R => `|x|) r (partial_function_total (projection_norm h2 xi))
      (beta * exterior_norm h2 (hBn n) xi)%:E
  | +oo%E => is_measure_essential_norm phi (fun x : R => `|x|)
      (partial_function_total (projection_norm h2 xi)) (beta * exterior_norm h2 (hBn n) xi)%:E
  | -oo%E => False
  end.
Proof.
case: t => [r| |] ht hb hphi hs //.
- by apply: projection_norm_lp=> //; rewrite -lee_fin.
- by rewrite hb mul1r; exact: projection_norm_essential.
Qed.

End ProjectionNorms.
