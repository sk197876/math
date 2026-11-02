(** Federer (1969), 2.5.14, p. 108: "however k need not be Phi almost
    unique, only locally so". Counterexample: X is the cartesian product of
    an uncountable discrete set D and R (DiscreteSliceSpace.v), E = R with
    the absolute value, Q = K(X), T = lambda, the product of the counting
    functional on K(D) and the integral on K(R) induced by the identity. All
    hypotheses of the vector modification of 2.5.12 in 2.5.14 hold, and
    every Radon measure Phi representing lambda is the variation measure.
    The constant density k = id and the density l, equal to -id on Z = D x
    {0} and to id elsewhere, are both normalised densities representing T.
    They agree locally Phi almost everywhere, as
    radon_vector_representation_locally_unique asserts, but Phi{x : k(x) <>
    l(x)} = Phi(Z) = infinity (DiscreteSliceRadon.v). Federer gives no
    example for this sentence; the example is supplied here. The local
    erratum has no entry for p. 108. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology normedtype.
From mathcomp Require Import lra.
From Federer Require Import RealMetricBackground RealNormUP NormMetric NormMetricScaleContinuity
  FunctionLatticeUP CompactSupportFunctionUP CompactSupportFunctionLattice FunctionLatticeSeminormUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum DaniellSpaceCompactness LatticeDominatedDifference
  ContinuousRadialSplitLaws ContinuousRadialSplit PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalBasic
  SummableRealFunctionUP MeasureIntegralUP RealIntegralFunctionalUP RadonMeasureUP
  CompactSupportRadonRepresentation LocallyNullMeasureUP LocallyNullMeasureLaws
  VectorDaniellHypotheses VectorDaniellRepresentationUP VectorDaniellNormalisationUP
  VectorDaniellDualExtension OrderBoundedVectorFunctionalUP RadonDualLocalModification
  TotalScalarMeasurability ScalarCountableEmbedding
  RadonVectorRepresentation DiscreteSliceSpace DiscreteSliceRadon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Scalar.
Variable R : realType.
Local Notation hN := (scalar_absolute_value_norm R).
Local Notation N := (fun y : R^o => `|y|).
Local Notation M := (real_norm_metric_space hN).

(** Source for [scalar_norm_separable]: hypothesis (1) of Federer
    2.5.12, p. 102, for E = R with the absolute value, as used in the
    counterexample of 2.5.14, p. 108: the rational numbers are dense. *)
Lemma scalar_norm_separable : is_separable_normed_space hN.
Proof.
exists ([set (ratr q : R) | q in [set: rat]] : set M); split.
  by apply: sub_countable (card_image_le _ _) _; exact: countableP.
move=> U [v hv] hU.
have hn : nbhs (v : M) U by rewrite openE in hU; exact: hU v hv.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (v : M) U) hn.
have he0 : 0 < e by exact: he.
have hve : (v : R) - e < (v : R) + e by lra.
have [q] := rat_in_itvoo hve; rewrite in_itv /= => /andP[hq1 hq2].
exists (ratr q : R); split; last by exists q.
apply: hb; change (`|(v : R) - ratr q| < e).
by rewrite ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [scalar_norm_to_line_continuous]: supporting comparison
    of topologies for Federer 2.5.14, p. 108: the identity map of R,
    from the metric of the absolute value to the real line, is
    continuous. *)
Lemma scalar_norm_to_line_continuous :
  continuous (fun y : M => (y : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R M _ _ 1 ler01)=> x y.
by rewrite real_line_metric_distanceE real_norm_metric_distanceE mul1r.
Qed.

(** Source for [scalar_line_to_norm_continuous]: supporting comparison
    of topologies for Federer 2.5.14, p. 108: the identity map of R,
    from the real line to the metric of the absolute value, is
    continuous. *)
Lemma scalar_line_to_norm_continuous :
  continuous (fun y : real_line_metric R => (y : M)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ M _ 1 ler01)=> x y.
by rewrite real_line_metric_distanceE real_norm_metric_distanceE mul1r.
Qed.

(** Source for [scalar_sign_dual]: supporting definition for the
    counterexample to almost uniqueness in Federer 2.5.14, p. 108: for
    a sign s, the functional y |-> s y belongs to E* of 2.5.12(2),
    p. 102. *)
Lemma scalar_sign_dual (s : R) : dual_space hN (fun y : R^o => s * y).
Proof.
split.
- by move=> a u v; rewrite /= mulrDr mulrCA.
- apply: (@metric_fixed_lipschitz_continuous R M _ _ `|s| (normr_ge0 s))=> x y.
  by rewrite real_line_metric_distanceE real_norm_metric_distanceE -mulrBr normrM.
Qed.

(** Source for [scalar_sign_dual_norm]: the dual norm of y |-> s y is
    one for s = 1 and s = -1, supporting the normalisation nu* o k = 1
    of Federer 2.5.12, p. 103, in the counterexample of 2.5.14, p. 108. *)
Lemma scalar_sign_dual_norm (s : R) : `|s| = 1 -> dual_norm N (fun y : R^o => s * y) = 1.
Proof.
move=> hs; rewrite /dual_norm.
set S := [set _ | _ in _].
have hmem : S 1.
  exists s=> //; rewrite -expr2 -real_normK ?num_real //; by rewrite hs expr1n.
have hub : ubound S 1.
  move=> _ [y hy <-]; apply: le_trans (ler_norm _) _.
  by rewrite normrM hs mul1r; move: hy=> /= ->.
apply/le_anti/andP; split; first exact: ge_sup (ex_intro _ _ hmem) hub.
exact: (ub_le_sup (ex_intro _ _ hub)) hmem.
Qed.
End Scalar.

Section Data.
Variable R : realType.
Variable D : choiceType.
Local Notation slice_space := (discrete_topology D * R)%type.
Local Notation KX := (@compactly_supported_continuous_functions R slice_space).
Local Notation hN := (scalar_absolute_value_norm R).
Local Notation N := (fun y : R^o => `|y|).
Local Notation lambda := (@slice_lambda R D).

(** Source for [slice_vector_space]: the space Q of the counterexample
    to almost uniqueness in Federer 2.5.14, p. 108: the members of K(X),
    regarded as maps of X into E = R. *)
Definition slice_vector_space : set (slice_space -> R^o) := [set w | KX (w : slice_space -> R)].

Local Notation Q := slice_vector_space.

(** Source for [slice_vector_space_laws]: Q is a vector space of maps
    of X into E, hypothesis (4) of Federer 2.5.12, p. 103, in the
    counterexample of 2.5.14, p. 108. *)
Lemma slice_vector_space_laws : is_vector_function_space Q.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R slice_space.
constructor.
- exact: compactly_supported_zero_function.
- by move=> w v hw hv; exact: (function_lattice_add hL hw hv).
- by move=> c w hw; exact: (compactly_supported_scale c hw).
Qed.

(** Source for [slice_lambda_linear]: lambda is linear on K(X), Federer
    2.5.13, p. 106, as used for T in the counterexample of 2.5.14,
    p. 108. *)
Lemma slice_lambda_linear : is_linear_functional_on_functions KX lambda.
Proof.
exact: daniell_compact_support_linear
  (monotone_daniell_integral_is_daniell (@slice_lambda_monotone_daniell R D)).
Qed.

(** Source for [slice_vector_lattice_module]: the clauses of hypothesis
    (4) of Federer 2.5.12, p. 103, for L = K(X), Q and E = R, in the
    counterexample of 2.5.14, p. 108. The last clause uses the radial
    splitting xi = (f / nu o w) w. *)
Lemma slice_vector_lattice_module : is_vector_lattice_module hN KX Q.
Proof.
have hL := @compactly_supported_continuous_functions_lattice R slice_space.
constructor.
- move=> f y hf; have h := compactly_supported_scale y hf.
  rewrite /Q /=; have -> : (fun x => f x *: y) = (fun x => y * f x) :> (slice_space -> R).
    by apply: funext=> x; rewrite mulrC.
  exact: h.
- move=> w alpha hw ha.
  have -> : (fun x => alpha (w x)) = (fun x => alpha 1 * w x).
    apply: funext=> x; rewrite mulrC -(dual_space_scale (w x) 1 ha).
    by congr (alpha _); rewrite /GRing.scale /= mulr1.
  exact: compactly_supported_scale.
- move=> w hw; have h := lattice_absolute_difference_member hL hw (compactly_supported_zero_function R slice_space).
  have -> : (fun x => `|w x|) = (fun x => `|w x - 0|) by apply: funext=> x; rewrite subr0.
  exact: h.
- move=> w f hw hf hb.
  have hwN : continuous (w : slice_space -> real_norm_metric_space hN).
    by move=> x; exact (continuous_comp (hw.1 x) (@scalar_line_to_norm_continuous R (w x))).
  have hxi := @norm_radial_split_continuous R slice_space R^o N hN w f hwN hf.1.1 hf.2 hb.
  exists (fun x => norm_radial_split N (w x) (f x)); split; last split.
  + split.
    * by move=> x; exact (continuous_comp (hxi x) (@scalar_norm_to_line_continuous R _)).
    * apply: (compact_support_unary_operation hf.1.2)=> x hfx.
      by rewrite /norm_radial_split hfx mul0r scale0r.
  + by move=> x; exact: (@norm_radial_split_norm R R^o N hN (w x) (f x) (hf.2 x) (hb x)).
  + by move=> x; exact: (@norm_radial_split_product R R^o N hN (w x) (f x)).
Qed.

(** Source for [slice_order_bounded_functional]: T = lambda satisfies
    the linearity and the finite bounds of hypothesis (5) of Federer
    2.5.12, p. 103, retained in 2.5.14, p. 108: lambda(w) <= lambda(f)
    whenever |w| <= f. *)
Lemma slice_order_bounded_functional : is_order_bounded_vector_functional N KX Q lambda.
Proof.
have hlin := slice_lambda_linear.
have hmon := @slice_lambda_monotone_daniell R D.
constructor.
- by move=> w v hw hv; exact: hlin.1.
- by move=> c w hw; exact: hlin.2.
- move=> f hf; exists (lambda f)=> w hw hle.
  apply: (monotone_daniell_integral_monotone hmon hw hf.1)=> x.
  exact: le_trans (ler_norm _) (hle x).
Qed.

(** Source for [slice_variation_integral]: the variation integral of T
    = lambda is lambda on K(X)+, Federer 2.5.12(5), p. 103, in the
    counterexample of 2.5.14, p. 108: f itself attains the supremum. *)
Lemma slice_variation_integral (f : slice_space -> R) : positive_function_lattice KX f ->
  variation_integral N Q lambda f = lambda f.
Proof.
move=> hf; rewrite /variation_integral.
set S := [set _ | _ in _].
have hmem : S (lambda f).
  exists f=> //; split; first exact: hf.1.
  by move=> x; rewrite /= ger0_norm ?(hf.2 x).
have hub : ubound S (lambda f).
  move=> _ [w [hw hle] <-].
  apply: (monotone_daniell_integral_monotone (@slice_lambda_monotone_daniell R D) hw hf.1)=> x.
  exact: le_trans (ler_norm _) (hle x).
apply/le_anti/andP; split; first exact: ge_sup (ex_intro _ _ hmem) hub.
exact: (ub_le_sup (ex_intro _ _ hub)) hmem.
Qed.
End Data.

Section Densities.
Variable R : realType.
Variable D : choiceType.
Local Notation slice_space := (discrete_topology D * R)%type.
Local Notation KX := (@compactly_supported_continuous_functions R slice_space).
Local Notation hN := (scalar_absolute_value_norm R).
Local Notation N := (fun y : R^o => `|y|).
Local Notation lambda := (@slice_lambda R D).
Local Notation Q := (@slice_vector_space R D).
Local Notation Z := (@zero_slice R D).

(** Source for [sign_dual]: supporting definition for the counterexample
    to almost uniqueness in Federer 2.5.14, p. 108: the member
    y |-> s y of E*, 2.5.12(2), p. 102, for E = R. *)
Definition sign_dual (s : R) : weak_dual_space hN :=
  exist _ (fun y : R^o => s * y) (mem_set (scalar_sign_dual s)).

(** Source for [slice_unit_density]: the density k = id of the
    counterexample to almost uniqueness in Federer 2.5.14, p. 108. *)
Definition slice_unit_density : slice_space -> weak_dual_space hN := fun _ => sign_dual 1.

(** Source for [slice_flipped_density]: the density l of the
    counterexample to almost uniqueness in Federer 2.5.14, p. 108,
    equal to -id on Z = D x {0} and to id elsewhere. *)
Definition slice_flipped_density : slice_space -> weak_dual_space hN :=
  fun x => if x.2 == 0 then sign_dual (-1) else sign_dual 1.

(** Source for [slice_densities_differ]: k and l differ exactly on
    Z = D x {0}, supporting Federer 2.5.14, p. 108. *)
Lemma slice_densities_differ (x : slice_space) :
  slice_unit_density x <> slice_flipped_density x <-> Z x.
Proof.
rewrite /slice_flipped_density /slice_unit_density /zero_slice.
case: eqP=> hx; split=> // _.
move=> h; have := congr1 (fun a : weak_dual_space hN => val a 1) h.
by rewrite /= !mulr1=> h1; lra.
Qed.

(** Source for [slice_densities_disagreement]: the set where k and l
    disagree is Z = D x {0}, supporting Federer 2.5.14, p. 108. *)
Lemma slice_densities_disagreement :
  ~` [set x | slice_unit_density x = slice_flipped_density x] = Z.
Proof. by apply/seteqP; split=> x /=; move/slice_densities_differ. Qed.

(** Source for [sign_dual_norm]: nu*(s id) = 1 for |s| = 1, Federer
    2.5.12, p. 103, in the counterexample of 2.5.14, p. 108. *)
Lemma sign_dual_norm (s : R) : `|s| = 1 -> dual_norm N (val (sign_dual s)) = 1.
Proof. exact: scalar_sign_dual_norm. Qed.

(** Source for [slice_densities_unit_norm]: both densities have unit
    dual norm at every point, Federer 2.5.12, p. 103, in the
    counterexample of 2.5.14, p. 108. *)
Lemma slice_densities_unit_norm (x : slice_space) :
  dual_norm N (val (slice_unit_density x)) = 1 /\ dual_norm N (val (slice_flipped_density x)) = 1.
Proof.
split; first by apply: sign_dual_norm; exact: normr1.
by rewrite /slice_flipped_density; case: eqP=> _; apply: sign_dual_norm; rewrite ?normrN normr1.
Qed.

Variable phi : set slice_space -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hr : is_radon_measure phi.
Hypothesis hA : is_real_integral_functional phi KX lambda.

(** Source for [slice_variation_represented]: Phi is the variation
    measure of T = lambda, Federer 2.5.12(5), p. 103, and 2.5.14,
    p. 108: it represents the variation integral on K(X)+. *)
Lemma slice_variation_represented :
  is_real_integral_functional phi (positive_function_lattice KX) (variation_integral N Q lambda).
Proof. by move=> f hf; rewrite slice_variation_integral //; exact: (@hA f hf.1). Qed.

(** Source for [slice_unit_norm_normalisation]: a density with unit
    dual norm everywhere satisfies the measurability and normalisation
    conclusions of Federer 2.5.12, p. 103, supporting 2.5.14, p. 108. *)
Lemma slice_unit_norm_normalisation (k : slice_space -> weak_dual_space hN) :
  (forall x, dual_norm N (val (k x)) = 1) ->
  is_measure_measurable_function phi (real_total_integrand (fun x => dual_norm N (val (k x)))) /\
  measure_almost_everywhere phi [set x | dual_norm N (val (k x)) = 1].
Proof.
move=> h; split.
- have -> : (fun x => dual_norm N (val (k x))) = (fun _ => 1) by apply: funext.
  exact (@scalar_real_integrand_measurable R _ phi hm (fun _ => 1)
    (@real_total_scalar_measurable R _ phi hm (fun _ => 1)
      (@measurable_total_constant R _ _ phi hm (1 : real_line_metric R)))).
- have -> : [set x | dual_norm N (val (k x)) = 1] = setT.
    by apply/seteqP; split=> x // _; exact: h.
  exact: measure_almost_everywhere_true hm.
Qed.

(** Source for [slice_unit_density_normalised]: k = id is a normalised
    density representing T = lambda, Federer 2.5.12, p. 103, as
    modified in 2.5.14, p. 108. *)
Lemma slice_unit_density_normalised :
  is_normalised_vector_daniell_density phi Q lambda slice_unit_density.
Proof.
have [hnm hae] := slice_unit_norm_normalisation (fun x => (slice_densities_unit_norm x).1).
constructor=> //.
- constructor.
  + exact (@measurable_total_constant R _ _ phi hm (sign_dual 1)).
  + move=> w hw.
    have -> : (fun x => val (slice_unit_density x) (w x)) = (w : slice_space -> R).
      by apply: funext=> x; rewrite /= mul1r.
    exact: (@hA w hw).
- by move=> x; rewrite (slice_densities_unit_norm x).1.
Qed.

(** Source for [slice_densities_locally_equal]: k = l locally Phi
    almost everywhere, Federer 2.5.14, p. 108, because they differ only
    on the locally null set Z = D x {0}. *)
Lemma slice_densities_locally_equal :
  measure_locally_almost_everywhere phi [set x | slice_unit_density x = slice_flipped_density x].
Proof.
rewrite /measure_locally_almost_everywhere slice_densities_disagreement.
exact: zero_slice_locally_null hm hr hA.
Qed.

(** Source for [slice_flipped_density_normalised]: l is a normalised
    density representing T = lambda, Federer 2.5.12, p. 103, as
    modified in 2.5.14, p. 108; the representation formula is preserved
    by the locally null change on Z. *)
Lemma slice_flipped_density_normalised :
  is_normalised_vector_daniell_density phi Q lambda slice_flipped_density.
Proof.
have [hnm hae] := slice_unit_norm_normalisation (fun x => (slice_densities_unit_norm x).2).
constructor=> //.
- exact: (radon_dual_locally_equal_representation hm hr (@slice_vector_lattice_module R D)
    slice_densities_locally_equal (normalised_vector_density_laws slice_unit_density_normalised)).
- by move=> x; rewrite (slice_densities_unit_norm x).2.
Qed.

Hypothesis hD : ~ countable [set: D].

(** Source for [slice_densities_not_almost_unique]: "however k need not
    be Phi almost unique, only locally so", Federer 2.5.14, p. 108.
    Counterexample for every Radon measure Phi representing lambda: the
    normalised densities k and l represent T, they agree locally almost
    everywhere by radon_vector_representation_locally_unique, and they
    differ on a set of infinite Phi measure. *)
Theorem slice_densities_not_almost_unique :
  [/\ is_normalised_vector_daniell_density phi Q lambda slice_unit_density,
    is_normalised_vector_daniell_density phi Q lambda slice_flipped_density,
    measure_locally_almost_everywhere phi
      [set x | slice_unit_density x = slice_flipped_density x],
    phi (~` [set x | slice_unit_density x = slice_flipped_density x]) = +oo%E &
    ~ measure_almost_everywhere phi [set x | slice_unit_density x = slice_flipped_density x]].
Proof.
have hk := slice_unit_density_normalised.
have hl := slice_flipped_density_normalised.
have hinf : phi (~` [set x | slice_unit_density x = slice_flipped_density x]) = +oo%E.
  by rewrite slice_densities_disagreement; exact: zero_slice_infinite hm hr hA hD.
split=> //.
- exact: (radon_vector_representation_locally_unique (@scalar_norm_separable R) hm hr
    (@slice_vector_lattice_module R D) slice_variation_represented
    (normalised_vector_density_laws hk) (normalised_vector_density_laws hl)).
- by rewrite /measure_almost_everywhere hinf.
Qed.
End Densities.

(** Source for [radon_vector_density_need_not_be_almost_unique]: "however
    k need not be Phi almost unique, only locally so", Federer 2.5.14,
    p. 108. Direct formalisation of the existential reading: there are
    a locally compact Hausdorff space X, a separable normed space E, a
    space Q and a functional T satisfying all hypotheses of the vector
    modification of 2.5.12 in 2.5.14 (radon_vector_representation), a
    Radon measure Phi representing the variation integral of T, and two
    normalised densities k and l representing T which agree locally Phi
    almost everywhere but differ on a set of infinite Phi measure. *)
Theorem radon_vector_density_need_not_be_almost_unique (R : realType) (D : choiceType) :
  ~ countable [set: D] ->
  exists (Q : set ((discrete_topology D * R)%type -> R^o))
    (T : ((discrete_topology D * R)%type -> R^o) -> R)
    (phi : set (discrete_topology D * R)%type -> \bar R)
    (k l : (discrete_topology D * R)%type -> weak_dual_space (scalar_absolute_value_norm R)),
  [/\ (hausdorff_space (discrete_topology D * R)%type /\
      locally_compact [set: (discrete_topology D * R)%type]) /\
      (is_separable_normed_space (scalar_absolute_value_norm R) /\ is_vector_function_space Q /\
      is_vector_lattice_module (scalar_absolute_value_norm R)
        (@compactly_supported_continuous_functions R (discrete_topology D * R)%type) Q /\
      is_order_bounded_vector_functional (fun y : R^o => `|y|)
        (@compactly_supported_continuous_functions R (discrete_topology D * R)%type) Q T),
    is_measure phi /\ is_radon_measure phi /\
      is_real_integral_functional phi
        (positive_function_lattice
          (@compactly_supported_continuous_functions R (discrete_topology D * R)%type))
        (variation_integral (fun y : R^o => `|y|) Q T),
    is_normalised_vector_daniell_density phi Q T k /\ is_normalised_vector_daniell_density phi Q T l,
    measure_locally_almost_everywhere phi [set x | k x = l x] &
    phi (~` [set x | k x = l x]) = +oo%E /\ ~ measure_almost_everywhere phi [set x | k x = l x]].
Proof.
move=> hD.
have [phi [hm [hr hA]]] := compact_support_radon_representation (@slice_space_hausdorff R D)
  (@slice_space_locally_compact R D) (@slice_lambda_monotone_daniell R D).
have [hk hl hloc hinf hnot] := slice_densities_not_almost_unique hm hr hA hD.
exists (@slice_vector_space R D), (@slice_lambda R D), phi,
  (@slice_unit_density R D), (@slice_flipped_density R D).
split=> //.
- split; first by split; [exact: slice_space_hausdorff|exact: slice_space_locally_compact].
  split; first exact: scalar_norm_separable.
  split; first exact: slice_vector_space_laws.
  split; first exact: slice_vector_lattice_module.
  exact: slice_order_bounded_functional.
- split=> //; split=> //; exact: slice_variation_represented hA.
Qed.
