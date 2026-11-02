(** Federer (1969), 2.7.16, example (2), printed p. 136: "the monomorphisms
    form an open subset of X ... Moreover G acts transitively on the set of
    monomorphisms." With the conditions of 2.7.1, p. 121, this makes the set
    M of monomorphisms of X = Hom(U, V), dim U = m <= dim V = n, a
    homogeneous space of the linear group G of V, and phi over M is
    |det|^{-m} covariant; Federer leaves these consequences implicit. This
    module proves that M, with the relative topology (set_type), is a
    locally compact Hausdorff space, that A(g, f) = g o f is continuous on G
    x M (composition is continuous, by ||g o f|| <= ||g|| . ||f||, 1.7.6, p.
    33), compatible and transitive, and that the orbit maps g |-> g o f are
    open: if L is a left inverse of f (L o f = 1_U, from a base of V
    extending f(e_1), ..., f(e_m), 1.6.1, p. 23), then h = g + (k - g o f) o
    L satisfies h o f = k and ||h - g|| <= ||k - g o f|| . ||L||
    (hom_monomorphisms_homogeneous). For a Haar integral mu of the additive
    group of X the integral nu(u) = mu(u') over M (u' the extension by 0) is
    a monotone Daniell integral on K(M) satisfying nu(u o A_g) = |det
    g|^{-m} nu(u) (monomorphism_haar_covariant), and the K(M) regular
    measure associated with it is a |det|^{-m} covariant measure over M in
    the sense of 2.7.1, p. 122 (monomorphism_covariant_measure). The
    identification of this measure with the restriction of phi to M is not
    formalised. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module ring.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis
  FiniteIndependence FiniteBasisComparison FiniteDualDimension Annihilator SimpleAdaptedBasis
  TensorUP Hom HomInner CoefficientCoordinates MeasureUP CompactSupportFunctionUP
  FunctionLatticeRegularityUP RealIntegralFunctionalUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum
  CovariantIntegralUP
  CovariantIntegralLaws HaarIntegralUP TopologicalGroupUP TopologicalProductMaps HomogeneousSpaceUP
  HomeomorphismUP SubtypeCompactHausdorff IsotropyGroupTopology HomSpaceTopology LinearGroupTopology
  LinearGroupSealed GeneralLinearPunctured OpenSubspaceExtension HomCompositionDeterminant
  HomHaarCovariance HomMonomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section MixedOperatorNorm.
Variable R : realType.
Variables U V W : lmodType R.
Variables (CU : U -> U -> R) (CV : V -> V -> R) (CW : W -> W -> R).
Hypotheses (hU : is_inner_product CU) (hV : is_inner_product CV) (hW : is_inner_product CW).
Variables (m n : nat) (c : 'I_m -> U) (b : 'I_n -> V).
Hypotheses (hc : is_basis c) (hb : is_basis b).

(** Source for [hom_operator_norm_comp_mixed]: ||f o g|| <= ||f|| . ||g||
    for g in Hom(U, V) and f in Hom(V, W), Federer 1.7.6, p. 33, and
    2.7.16, p. 134. Supporting lemma. *)
Lemma hom_operator_norm_comp_mixed (f : Hom V W) (g : Hom U V) :
  hom_operator_norm hU hW hc (hom_comp f g) <=
    hom_operator_norm hV hW hb f * hom_operator_norm hU hV hc g.
Proof.
apply: hom_operator_norm_least; first by rewrite mulr_ge0 ?hom_operator_norm_nonnegative.
move=> x; rewrite hom_compE.
apply: le_trans (hom_operator_norm_bound hV hW hb f (g x)) _.
rewrite -mulrA ler_wpM2l ?hom_operator_norm_nonnegative //.
exact: hom_operator_norm_bound.
Qed.

End MixedOperatorNorm.

Section LeftComposition.
Variable R : realType.
Variables U V : lmodType R.
Variable C : U -> U -> R.
Hypothesis hC : is_inner_product C.
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation X := (inner_metric_space (hom_inner_productP hC hB hc)).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation onormX := (hom_operator_norm hC hB hc).
Local Notation onormH := (hom_operator_norm hB hB hb).

(** Source for [hom_left_composition_continuous]: (g, f) |-> g o f is
    continuous on Hom(V, V) x Hom(U, V), since g o f - h o k =
    (g - h) o f + h o (f - k) and ||g o f|| <= ||g|| . ||f||, Federer
    2.7.16, p. 134, applied to the action of 2.7.16, p. 136. Supporting
    theorem. *)
Theorem hom_left_composition_continuous :
  continuous (fun p : H * X => (hom_comp (p.1 : Hom V V) (p.2 : Hom U V) : X)).
Proof.
move=> [f g] A /hom_space_nbhs_operator [r hr hA].
pose d := Num.min 1 (r / (onormH f + onormX g + 1)).
have hc0 : 0 < onormH f + onormX g + 1.
  by apply: ltr_wpDl; [rewrite addr_ge0 ?hom_operator_norm_nonnegative|exact: ltr01].
have hd : 0 < d by rewrite /d lt_min ltr01 divr_gt0.
have hd1 : d <= 1 by rewrite /d ge_min lexx.
have hdc : d * (onormH f + onormX g + 1) <= r by rewrite -ler_pdivlMr // /d ge_min lexx orbT.
exists ([set h : H | onormH (h - f) < d], [set k : X | onormX (k - g) < d]).
  by split; exact: hom_space_operator_ball_nbhs.
move=> [h k] [/= hh hk]; apply: hA.
have he : (hom_comp (h : Hom V V) (k : Hom U V) : X) - hom_comp (f : Hom V V) (g : Hom U V) =
    hom_comp (h - f : H) (k : Hom U V) + hom_comp (f : Hom V V) (k - g : X).
  apply: hom_ext=> x; rewrite hom_addE !hom_compE.
  have -> : ((hom_comp (h : Hom V V) (k : Hom U V) : X) - hom_comp (f : Hom V V) (g : Hom U V) : Hom U V) x =
    h (k x) - f (g x) by [].
  have -> : ((h - f : H) : Hom V V) (k x) = h (k x) - f (k x) by [].
  have -> : ((k - g : X) : Hom U V) x = k x - g x by [].
  rewrite (linearB (hom_as_linear f)) /=.
  by rewrite addrA subrK.
rewrite he; apply: le_lt_trans (hom_operator_norm_add hC hB hc _ _) _.
have hkn : onormX k <= onormX g + 1.
  apply: le_trans (hom_operator_norm_sub_bound hC hB hc g k) _; rewrite lerD2l.
  exact: le_trans (ltW hk) hd1.
apply: (@lt_le_trans _ _ (d * (onormH f + onormX g + 1))); last exact: hdc.
apply: (@le_lt_trans _ _ (onormH (h - f) * (onormX g + 1) + onormH f * onormX (k - g))).
  apply: lerD.
    apply: le_trans (hom_operator_norm_comp_mixed hC hB hB hc hb _ _) _.
    by rewrite ler_wpM2l ?hom_operator_norm_nonnegative.
  exact: (hom_operator_norm_comp_mixed hC hB hB hc hb).
rewrite (_ : d * (onormH f + onormX g + 1) = d * (onormX g + 1) + d * onormH f); last first.
  by ring.
have hg1 : 0 < onormX g + 1.
  by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
apply: ltr_leD; first by rewrite ltr_pM2r.
by rewrite mulrC ler_wpM2r ?hom_operator_norm_nonnegative // ltW.
Qed.

End LeftComposition.

Section MonomorphismSpace.
Variable R : realType.
Variables U V : lmodType R.
Variable C : U -> U -> R.
Hypothesis hC : is_inner_product C.
Variable m : nat.
Variable c : 'I_m -> U.
Hypothesis hc : is_basis c.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Hypothesis hmn : (m <= n)%N.
Local Notation X := (inner_metric_space (hom_inner_productP hC hB hc)).
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation M := (set_type (hom_monomorphisms hC hc hB)).
Local Notation A := (hom_linear_group_action hC hc hB hb).
Local Notation onormX := (hom_operator_norm hC hB hc).
Local Notation onormH := (hom_operator_norm hB hB hb).
Local Notation onormL := (hom_operator_norm hB hC hb).
Local Notation KM := (@compactly_supported_continuous_functions R M).
Local Notation KX := (@compactly_supported_continuous_functions R X).

(** Source for [monomorphism_space_hausdorff]: the set of monomorphisms
    is Hausdorff, as required of a homogeneous space in Federer 2.7.1,
    p. 121. Supporting lemma. *)
Lemma monomorphism_space_hausdorff : hausdorff_space M.
Proof. by apply: set_type_hausdorff; exact: hom_space_hausdorff. Qed.

(** Source for [monomorphism_space_locally_compact]: the set of
    monomorphisms is locally compact, as required in Federer 2.7.1,
    p. 121: it is open in X, whose closed balls are compact
    (HomSpaceTopology.v). Supporting lemma. *)
Lemma monomorphism_space_locally_compact : locally_compact [set: M].
Proof.
apply: open_subspace_locally_compact; last exact: hom_monomorphisms_open hb.
by move=> a r; exact: (hom_space_closed_ball_compact hb).
Qed.

(** Source for [action_monomorphism]: g o f is a monomorphism whenever
    g in G and f is one, Federer 2.7.16, p. 136. Supporting lemma. *)
Lemma action_monomorphism (g : GL) (f : M) : hom_monomorphisms hC hc hB (A g (set_val f)).
Proof.
move=> x y; rewrite /A /hom_linear_group_action !hom_compE=> /(set_valP g) h.
exact: (set_valP f) h.
Qed.

(** Source for [monomorphism_action]: the action A(g, f) = g o f of G
    on the set of monomorphisms, Federer 2.7.16, p. 136. Definition. *)
Definition monomorphism_action (g : GL) (f : M) : M :=
  exist _ (A g (set_val f)) (mem_set (@action_monomorphism g f)).

(** Source for [monomorphism_action_continuous]: the action is
    continuous on G x M, Federer 2.7.1, p. 121, by the continuity of
    composition. Supporting lemma. *)
Lemma monomorphism_action_continuous : continuous (fun p : GL * M => monomorphism_action p.1 p.2).
Proof.
apply: set_type_continuous_into.
have -> : set_val \o (fun p : GL * M => monomorphism_action p.1 p.2) =
    (fun q : H * X => (hom_comp (q.1 : Hom V V) (q.2 : Hom U V) : X)) \o
      (fun p : GL * M => ((set_val p.1 : H), (set_val p.2 : X))) by [].
have hp : continuous (fun p : GL * M => ((set_val p.1 : H), (set_val p.2 : X))).
  apply: (@topological_pair_continuous (GL * M)%type H X).
  - move=> q; exact: continuous_comp (@first_projection_continuous GL M q)
      (@set_type_val_continuous H _ q.1).
  - move=> q; exact: continuous_comp (@second_projection_continuous GL M q)
      (@set_type_val_continuous X _ q.2).
move=> p; apply: continuous_comp; first exact: hp.
exact: hom_left_composition_continuous.
Qed.

(** Source for [monomorphism_action_compatible]: A(g h, f) =
    A(g, A(h, f)), Federer 2.7.1, p. 121. Supporting lemma. *)
Lemma monomorphism_action_compatible (g h : GL) (f : M) :
  monomorphism_action (mul g h) f = monomorphism_action g (monomorphism_action h f).
Proof. by apply: val_inj; rewrite /= hom_linear_group_action_compatible. Qed.

(** Source for [monomorphism_orbit_onto]: "G acts transitively on the
    set of monomorphisms", Federer 2.7.16, p. 136, as im A^f = M,
    2.7.1, p. 121. Supporting lemma. *)
Lemma monomorphism_orbit_onto (f : M) : orbit_map monomorphism_action f @` setT = setT.
Proof.
apply/seteqP; split=> // k _.
have [g hg] := hom_monomorphisms_transitive hC hc hB hb hmn (set_valP f) (set_valP k).
by exists g=> //; apply: val_inj.
Qed.

(** Source for [monomorphism_left_inverse]: every monomorphism f has a
    left inverse L in Hom(V, U), L o f = 1_U: extend f(e_1), ..., f(e_m)
    to a base v of V (1.6.1, p. 23) and put L(v_k) = e_k for k <= m,
    L(v_k) = 0 otherwise; supporting the openness of the orbit maps,
    Federer 2.7.1, p. 121, for the action of 2.7.16, p. 136. Supporting
    lemma. *)
Lemma monomorphism_left_inverse (f : Hom U V) : injective f ->
  exists L : Hom V U, forall x, L (f x) = x.
Proof.
move=> hf.
have hi := finite_independent_map (f := hom_as_linear f) hf (finite_basis_independent hc).
have [v [hv hv1]] := finite_basis_extension_fixed hmn hi hb.
exists (\sum_k hom_with_coefficient (c k) (dual_basis hv (widen_ord hmn k)))=> x.
apply: (basis_linear_ext hc (hom_as_linear (hom_comp (\sum_k hom_with_coefficient (c k)
  (dual_basis hv (widen_ord hmn k))) f)) (linear_id U))=> j.
rewrite hom_as_linearE hom_compE /=.
have -> : f (c j) = v (widen_ord hmn j) by rewrite hv1.
rewrite hom_sum_coefficientsE.
under eq_bigr do rewrite hom_with_coefficientE dual_basisE.
rewrite (bigD1 j) //= eqxx scale1r big1 ?addr0 // => k hk.
have hne : (widen_ord hmn j == widen_ord hmn k) = false.
  by rewrite -val_eqE /= val_eqE eq_sym (negbTE hk).
by rewrite hne scale0r.
Qed.

(** Source for [monomorphism_orbit_open]: "for each x in X the map
    A^x: G -> X ... is open", Federer 2.7.1, p. 121, for the action of G
    on the monomorphisms, 2.7.16, p. 136: if L o f = 1_U, U is open in G,
    g in U and k is a monomorphism with ||k - g o f|| ||L|| small, then
    h = g + (k - g o f) o L lies in U and h o f = k. Direct
    formalisation. *)
Theorem monomorphism_orbit_open (f : M) : is_open_map (orbit_map monomorphism_action f).
Proof.
move=> O hO; rewrite openE=> y [g hgO <-]; rewrite /interior.
have [O' hO' hO'O] := hO.
have hgO' : O' (set_val g) by rewrite -hO'O in hgO.
have hOG : nbhs (set_val g : H) (O' `&` linear_group hB hb).
  apply: open_nbhs_nbhs; split; first exact: openI hO' (linear_group_set_open (hB := hB) (hb := hb)).
  by split=> //; exact: set_valP.
have [r hr hrO] := (hom_space_nbhs_operator _ _).1 hOG.
have [L hL] := monomorphism_left_inverse (set_valP f).
pose l := onormL L + 1.
have hl : 0 < l by apply: ltr_wpDl; [exact: hom_operator_norm_nonnegative|exact: ltr01].
have hd : 0 < r / l by rewrite divr_gt0.
have hnb := @set_type_val_continuous X _ (orbit_map monomorphism_action f g) _
  (hom_space_operator_ball_nbhs (set_val (orbit_map monomorphism_action f g) : X) hd).
apply: (@filterS _ _ (nbhs_filter _) _ _ _ hnb)=> z /= hz.
pose gf : Hom U V := hom_comp (set_val g : Hom V V) (set_val f : Hom U V).
pose h : Hom V V := (set_val g : Hom V V) + hom_comp ((set_val z : X) - (gf : X) : Hom U V) L.
have hz' : onormX ((set_val z : X) - (gf : X)) < r / l by exact: hz.
have hw : onormH ((h : H) - set_val g) < r.
  have -> : (h : H) - set_val g = hom_comp ((set_val z : X) - (gf : X) : Hom U V) L.
    by rewrite /h addrC addKr.
  apply: le_lt_trans (hom_operator_norm_comp_mixed hB hC hB hb hc _ _) _.
  apply: (@le_lt_trans _ _ (onormX ((set_val z : X) - (gf : X)) * l)).
    by rewrite ler_wpM2l ?hom_operator_norm_nonnegative // /l lerDl ler01.
  by rewrite -ltr_pdivlMr.
have [hhO hhG] := hrO (h : H) hw.
exists (exist _ (h : H) (mem_set hhG)); first by rewrite -hO'O.
apply: val_inj; rewrite /= /hom_linear_group_action; apply: hom_ext=> x.
rewrite hom_compE /h hom_addE hom_compE hL.
have -> : (((set_val z : X) - (gf : X) : X) : Hom U V) x = (set_val z : Hom U V) x - gf x by [].
by rewrite /gf hom_compE addrC subrK.
Qed.

(** Source for [hom_monomorphisms_homogeneous]: the set of monomorphisms
    of X = Hom(U, V), m <= n, is a homogeneous space of the linear group
    G of V through A(g, f) = g o f, in the sense of Federer 2.7.1,
    p. 121; "G acts transitively on the set of monomorphisms", 2.7.16,
    p. 136. Direct formalisation. *)
Theorem hom_monomorphisms_homogeneous : is_homogeneous_space mul monomorphism_action.
Proof.
split.
- exact: monomorphism_action_continuous.
- exact: monomorphism_action_compatible.
- exact: monomorphism_orbit_open.
- exact: monomorphism_orbit_onto.
Qed.

(** Source for [extension_monomorphism_action]: (u o A_g)' = u' o A_g
    for u on the set of monomorphisms, extended by 0 to X: g o f is a
    monomorphism if and only if f is; supporting "phi is |det|^{-m}
    covariant", Federer 2.7.16, p. 136. Supporting lemma. *)
Lemma extension_monomorphism_action (u : M -> R) (g : GL) :
  open_extension (u \o monomorphism_action g) = open_extension u \o A g.
Proof.
apply: funext=> f /=.
case: (pselect (hom_monomorphisms hC hc hB f))=> hf.
- pose y : M := exist _ f (mem_set hf).
  rewrite -[f]/(set_val y) open_extensionE.
  have -> : A g (set_val y) = set_val (monomorphism_action g y) by [].
  by rewrite open_extensionE.
- rewrite !open_extension_out //.
  by move=> hgf; apply: hf=> x x' hx; apply: hgf; rewrite /A /hom_linear_group_action !hom_compE hx.
Qed.

Section HaarIntegral.
Variable mu : (X -> R) -> R.
Hypothesis hmu : is_left_haar_integral (fun f g : X => f + g) mu.

(** Source for [monomorphism_restricted_monotone]: u |-> mu(u') is a
    monotone Daniell integral on K(M), Federer 2.5.2, p. 92, the integral
    over the open set M of monomorphisms, 2.7.16, p. 136. Supporting
    lemma. *)
Lemma monomorphism_restricted_monotone :
  is_monotone_daniell_integral KM (open_restricted_integral mu).
Proof.
exact: (open_restricted_monotone (hom_space_hausdorff (hb := hc)) (hom_monomorphisms_open hC hc hB hb)
  (nonzero_invariant_integral_monotone hmu)).
Qed.

(** Source for [monomorphism_haar_covariant]: phi over the set M of
    monomorphisms is |det|^{-m} covariant, Federer 2.7.16, p. 136, for
    the integral: nu(u o A_g) = |det g|^{-m} nu(u) whenever u in K(M),
    g in G, where nu(u) = mu(u'). Direct formalisation for the
    associated integral. *)
Theorem monomorphism_haar_covariant :
  is_covariant_integral monomorphism_action (fun g => `|linear_group_det hB hb g| ^- m)
    (open_restricted_integral mu).
Proof.
split; first exact: monotone_daniell_integral_is_daniell monomorphism_restricted_monotone.
move=> u g hu; rewrite /open_restricted_integral extension_monomorphism_action.
have h := covariant_integral_law (hom_haar_integral_covariant hC hc hB hb hmu) g
  (open_extension_compact (hom_space_hausdorff (hb := hc)) (hom_monomorphisms_open hC hc hB hb) hu).
exact h.
Qed.

(** Source for [monomorphism_covariant_measure]: the K(M) regular
    measure associated with nu is a |det|^{-m} covariant measure over the
    homogeneous space M of monomorphisms, Federer 2.7.1, p. 122, and
    2.7.16, p. 136. Direct formalisation; the measure is characterised
    by its integral nu(u) = int u' dphi, not identified with the
    restriction of phi. *)
Theorem monomorphism_covariant_measure :
  exists psi : set M -> \bar R,
    is_covariant_measure monomorphism_action (fun g => `|linear_group_det hB hb g| ^- m) psi /\
    is_real_integral_functional psi KM (open_restricted_integral mu).
Proof.
have [psi [hpsi _ hi _ _]] := covariant_measure_exists monomorphism_restricted_monotone
  (covariant_integral_law monomorphism_haar_covariant).
by exists psi.
Qed.

End HaarIntegral.

End MonomorphismSpace.

Arguments monomorphism_action {R U V C} hC {m c} hc {B} hB {n b} hb g f.
Arguments monomorphism_haar_covariant {R U V C} hC {m c} hc {B} hB {n b} hb {mu} _.
Arguments monomorphism_covariant_measure {R U V C} hC {m c} hc {B} hB {n b} hb {mu} _.
