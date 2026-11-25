(** Federer (1969), 2.7.16, example (5), printed p. 138: "If G is the affine
    group of R^n, then Delta_G(g) = |det L(g)|^{-1} whenever g in G. To
    prove this we note first that ker L|G = im tau is abelian, hence
    Delta_G|ker L = 1. Then we observe that L^n is |det o L|^{-1} covariant
    with respect to the usual action of G on R^n, with G^0 = GL(n, R), hence
    |det o L|^{-1} and Delta_G agree on GL(n, R)." The affine group is that
    of AffineGroupTopology.v: pairs p = (g, z) of GL(V) x V standing for
    tau_z o g, so that L(p) = g and p is univalent; V is a space with an
    inner product and a finite basis, and R^n is the instance with the inner
    product of 1.7.1 and the standard basis. The proof follows Federer. The
    translations (1_V, z) form the closed normal abelian subgroup ker L, so
    Delta_G = 1 on it (GroupIsomorphismModular.v, by 2.7.12, p. 129). Every
    Haar integral mu of the additive group of V (for R^n, u |-> int u dL^n)
    satisfies mu(u o A_p) = |det g|^{-1} mu(u) for the usual action A_p(v) =
    z + g(v), by translation invariance and mu(u o g) = |det g|^{-1} mu(u)
    (FiniteHaarLinear.v, from example (1)). Weil's condition 2.7.11(1), p.
    128, at the point 0, whose isotropy group G^0 = {(g, 0)} is isomorphic
    to GL(V), gives Delta_G(g, 0) = |det g|^{-1} Delta_{G^0}(g, 0) = |det
    g|^{-1}, since Delta_{GL(V)} = 1 (example (2), LinearGroupUnimodular.v).
    Finally (g, z) = (1_V, z)(g, 0). The local erratum has no entry for this
    passage of p. 138. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis
  TensorUP Hom HomInner FiniteCoordinates EuclideanInnerProduct GrassmannAbbreviations ExteriorDeterminant
  MeasureUP RealIntegralFunctionalUP FunctionLatticeRegularityUP CompactSupportFunctionUP DaniellIntegralUP
  MonotoneDaniellIntegralUP DaniellSpacePushforward ProperMapUP HomeomorphismUP EquivariantPushforward
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  HomogeneousSpaceLaws GroupMultiplicationHomogeneous CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  HaarIntegralExistence ModularFunctionUP ModularFunction UnimodularGroupUP UnimodularGroups NormalSubgroupUP
  WeilCondition HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance LinearGroupUnimodular
  FiniteHaarLinear EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueHaar EuclideanAdditiveGroup AffineGroupTopology GroupIsomorphismModular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AffineModular.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation AG := (GL * VT)%type.
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation amul := (affine_group_mul hB hb).
Local Notation ainv := (affine_group_inv hB hb).
Local Notation aunit := (affine_group_unit hB hb).
Local Notation A := (affine_group_action hB hb).
Local Notation det := (linear_group_det hB hb).
Local Notation KV := (@compactly_supported_continuous_functions R VT).

(** Source for [hAG]: the affine group is a locally compact Hausdorff
    topological group, Federer 2.7.16, p. 134, used in this section. *)
Let hAG : is_locally_compact_hausdorff_group amul ainv aunit := affine_group_lch hB hb.
(** Source for [hgl]: the group laws of GL(V), Federer 2.7.16, p. 134,
    used in this section. *)
Let hgl := linear_group_group_laws hG.

(** Source for [inner_additive_lch_group]: the additive group of V is
    a locally compact Hausdorff topological group, Federer 2.7.16,
    p. 134, as required for its Haar integrals in 2.7.2, p. 122.
    Supporting lemma. *)
Lemma inner_additive_lch_group : is_locally_compact_hausdorff_group (fun x y : VT => x + y) (fun x => - x) 0.
Proof.
split.
- split; first by split; [exact: addrA|exact: add0r|exact: addNr].
  + exact: add_continuous.
  + exact: oppr_continuous.
- exact: (@inner_space_hausdorff R V B hB).
- exact: (inner_space_locally_compact hb).
Qed.

(** Source for [affine_linear_character]: the function
    |det o L|^{-1} on the affine group, Federer 2.7.16, p. 138.
    Definition. *)
Definition affine_linear_character (p : AG) : R := `|det p.1|^-1.

(** Source for [affine_linear_character_mul]: |det o L|^{-1} is a
    homomorphism of G into R ~ {0}, Federer 1.3.4, p. 16, as required
    of chi in 2.7.1, p. 122, since L(p q) = L(p) o L(q). Supporting
    lemma. *)
Lemma affine_linear_character_mul (p q : AG) :
  affine_linear_character (amul p q) = affine_linear_character p * affine_linear_character q.
Proof. by rewrite /affine_linear_character /= linear_group_det_mul normrM invfM. Qed.

(** Source for [affine_linear_character_nonzero]: |det o L|^{-1} does
    not vanish, Federer 1.3.4, p. 16. Supporting lemma. *)
Lemma affine_linear_character_nonzero (p : AG) : affine_linear_character p != 0.
Proof. by rewrite /affine_linear_character invr_eq0 normr_eq0 linear_group_det_nonzero. Qed.

(** Source for [affine_linear_character_continuous]: |det o L|^{-1} is
    continuous, Federer 2.7.16, pp. 134–138. Supporting lemma. *)
Lemma affine_linear_character_continuous : continuous (affine_linear_character : AG -> real_line_metric R).
Proof.
have hd := @linear_group_det_power_continuous R V B hB n b hb 1.
have -> : (affine_linear_character : AG -> real_line_metric R) =
    (fun g : GL => `|det g| ^- 1 : real_line_metric R) \o (@fst GL VT).
  by apply: funext=> p; rewrite /affine_linear_character /= expr1.
move=> p; apply: continuous_comp; first exact: first_projection_continuous.
exact: hd.
Qed.

(** Source for [affine_haar_integral_covariant]: "L^n is |det o L|^{-1}
    covariant with respect to the usual action of G on R^n", Federer
    2.7.16, p. 138, for every Haar integral mu of the additive group of
    V: mu(u o A_p) = |det g|^{-1} mu(u) for p = (g, z), since
    u o A_p = (u o tau_z) o g, mu(u o tau_z) = mu(u) and
    mu(w o g) = |det g|^{-1} mu(w) (finite_haar_integral_linear).
    Direct formalisation. *)
Theorem affine_haar_integral_covariant (mu : (VT -> R) -> R) :
  is_left_haar_integral (fun x y : VT => x + y) mu -> is_covariant_integral A affine_linear_character mu.
Proof.
move=> hmu.
have hT := lch_group_topological inner_additive_lch_group.
have hLh := left_multiplication_homogeneous hT.
have hlaw := covariant_integral_law (nonzero_invariant_integral_invariant hmu).
split; first exact: (covariant_integral_daniell (nonzero_invariant_integral_invariant hmu)).
move=> u p hu.
have hut : KV (u \o left_multiplication_action (fun x y : VT => x + y) p.2).
  exact: (compactly_supported_translate (topological_group_laws hT) hLh _ hu).
have e1 : u \o A p = (u \o left_multiplication_action (fun x y : VT => x + y) p.2) \o
    (hom_as_linear (set_val p.1 : Hom V V) : VT -> VT) by [].
rewrite e1 (@finite_haar_integral_linear R V B hB n b hb mu (hom_as_linear (set_val p.1 : Hom V V)) hmu
  (linear_group_det_nonzero p.1) _ hut).
by rewrite (hlaw u p.2 hu) mul1r.
Qed.

(** Source for [affine_haar_integral_nonzero_covariant]: a nonzero
    |det o L|^{-1} covariant integral on K(V) exists, Federer 2.7.16,
    p. 138, with 2.7.5, p. 125. Supporting lemma. *)
Lemma affine_haar_integral_nonzero_covariant :
  exists mu : (VT -> R) -> R, is_covariant_integral A affine_linear_character mu /\ exists2 v, KV v & mu v <> 0.
Proof.
have [mu hmu] := left_haar_integral_exists R inner_additive_lch_group.
exists mu; split; first exact: affine_haar_integral_covariant.
exact: (nonzero_invariant_integral_nonzero hmu).
Qed.

Local Notation S0 := (isotropy_subgroup A 0).

(** Source for [affine_isotropy_member]: (g, 0) fixes 0, Federer
    2.7.16, p. 138, "G^0 = GL(n, R)". Supporting lemma. *)
Lemma affine_isotropy_member (g : GL) : S0 ((g, 0) : AG).
Proof. by rewrite /isotropy_subgroup /= /affine_group_action affine_group_map_zero. Qed.

(** Source for [affine_isotropy_of]: the member (g, 0) of G^0 for g in
    GL(n, R), "with G^0 = GL(n, R)", Federer 2.7.16, p. 138.
    Definition. *)
Definition affine_isotropy_of (g : GL) : S0 := exist _ ((g, 0) : AG) (mem_set (affine_isotropy_member g)).

(** Source for [affine_isotropy_translation]: the members of G^0 have
    translation part 0, Federer 2.7.16, p. 138. Supporting lemma. *)
Lemma affine_isotropy_translation (t : S0) : (set_val t).2 = 0.
Proof.
have h := set_valP t; rewrite /isotropy_subgroup /= in h.
by rewrite -(affine_group_map_zero (set_val t)); exact: h.
Qed.

(** Source for [affine_isotropy_homeomorphism]: g |-> (g, 0) is a
    homeomorphism of GL(n, R) onto G^0, "G^0 = GL(n, R)", Federer
    2.7.16, p. 138. Supporting lemma. *)
Lemma affine_isotropy_homeomorphism :
  is_homeomorphism_with_inverse affine_isotropy_of (fun t : S0 => (set_val t).1).
Proof.
split.
- apply: set_type_continuous_into=> g.
  apply: (@topological_pair_continuous GL GL VT (fun g => g) (fun _ => (0 : VT))); last first.
    exact: cst_continuous.
  by move=> h.
- move=> t; apply: (@continuous_comp S0 AG GL set_val (@fst GL VT)).
    exact: set_type_val_continuous.
  exact: first_projection_continuous.
- by move=> g.
- move=> t; apply: val_inj; rewrite /= -set_valE.
  have h := affine_isotropy_translation t.
  by case: (set_val t) h=> g z /= ->.
Qed.

Section Isotropy.
Variables (mul0 : S0 -> S0 -> S0) (inv0 : S0 -> S0) (e0 : S0).
Hypothesis h0 : is_subgroup_restriction amul ainv aunit S0 mul0 inv0 e0.

(** Source for [hl0]: G^0 is a locally compact Hausdorff topological
    group, Federer 2.7.10, p. 127, used in this section. *)
Let hl0 : is_locally_compact_hausdorff_group mul0 inv0 e0.
Proof.
apply: (subgroup_restriction_locally_compact_hausdorff h0 hAG).
exact: (isotropy_subgroup_closed (affine_group_homogeneous hB hb) (@inner_space_hausdorff R V B hB)).
Qed.

(** Source for [affine_isotropy_of_mul]: g |-> (g, 0) is a
    homomorphism of GL(n, R) into G^0, Federer 2.7.16, p. 138.
    Supporting lemma. *)
Lemma affine_isotropy_of_mul (g h : GL) :
  affine_isotropy_of (mul g h) = mul0 (affine_isotropy_of g) (affine_isotropy_of h).
Proof.
apply: val_inj; rewrite /= -!set_valE (subgroup_restriction_mul h0) /=.
rewrite /affine_group_mul /=.
by rewrite (linear0 (hom_as_linear (set_val g : Hom V V))) addr0.
Qed.

(** Source for [affine_isotropy_modular_unit]: "with G^0 = GL(n, R)",
    Federer 2.7.16, p. 138: Delta_{G^0} = 1, since G^0 is isomorphic to
    GL(n, R) and Delta_{GL(n, R)} = 1 (example (2), p. 137). Supporting
    lemma. *)
Lemma affine_isotropy_modular_unit (D0 : S0 -> R) : is_modular_function mul0 inv0 D0 -> forall t, D0 t = 1.
Proof.
move=> hD0 t.
have [DL hDL] := modular_function_exists R (linear_group_operations_lch hB hb).
have hiso := isomorphism_modular_function (linear_group_operations_lch hB hb) hl0
  affine_isotropy_homeomorphism affine_isotropy_of_mul hDL hD0.
have ht : t = affine_isotropy_of (set_val t).1.
  exact: esym (homeomorphism_right_inverse affine_isotropy_homeomorphism t).
by rewrite ht -hiso (linear_group_modular_unit hB hb hDL).
Qed.

End Isotropy.

(** Source for [affine_modular_linear_part]: "hence |det o L|^{-1} and
    Delta_G agree on GL(n, R)", Federer 2.7.16, p. 138: by Weil's
    condition 2.7.11(1), p. 128, for the nonzero |det o L|^{-1}
    covariant integral of affine_haar_integral_covariant and
    Delta_{G^0} = 1. Direct formalisation. *)
Theorem affine_modular_linear_part (DG : AG -> R) :
  is_modular_function amul ainv DG -> forall g : GL, DG (g, 0) = `|det g|^-1.
Proof.
move=> hDG g.
have [mul0 [inv0 [e0 [h0 hl0]]]] := isotropy_group_exists (0 : VT) hAG (affine_group_homogeneous hB hb)
  (@inner_space_hausdorff R V B hB).
have [D0 hD0] := modular_function_exists R hl0.
have [mu [hmu hmu0]] := affine_haar_integral_nonzero_covariant.
have hW := weil_condition_necessary hAG (affine_group_homogeneous hB hb) (@inner_space_hausdorff R V B hB) h0 hDG hD0
  affine_linear_character_mul affine_linear_character_nonzero affine_linear_character_continuous hmu hmu0.
have := hW (affine_isotropy_of g).
by rewrite (affine_isotropy_modular_unit h0 hD0) mulr1.
Qed.

(** Source for [affine_translations]: "ker L|G = im tau", Federer 2.7.16,
    p. 138: the pairs (1_V, z). Definition. *)
Definition affine_translations : set AG := [set p | p.1 = unit].

(** Source for [affine_translations_normal]: ker L|G is a normal
    subgroup of G, Federer 2.7.16, p. 138, as the kernel of the
    homomorphism L (2.7.12, p. 129). Supporting lemma. *)
Lemma affine_translations_normal : is_normal_subgroup amul ainv aunit affine_translations.
Proof.
split; first split.
- by [].
- move=> p q hp hq; rewrite /affine_translations /= in hp hq *.
  by rewrite hp hq (group_mul1g hgl).
- move=> p hp; rewrite /affine_translations /= in hp *.
  by rewrite hp (group_inv1 hgl).
- move=> p s hs; rewrite /affine_translations /= in hs *.
  by rewrite hs (group_mulg1 hgl) (group_mulgV hgl).
Qed.

(** Source for [affine_translations_closed]: ker L|G is closed in G,
    Federer 2.7.16, p. 138, the preimage of {1_V} under the continuous
    map L, GL(n, R) being Hausdorff. Supporting lemma. *)
Lemma affine_translations_closed : closed affine_translations.
Proof.
have hH := lch_group_hausdorff (linear_group_operations_lch hB hb).
have hx : closed [set unit] by exact: accessible_closed_set1 (hausdorff_accessible hH) unit.
have -> : affine_translations = (@fst GL VT) @^-1` [set unit] by [].
by apply: preimage_closed hx=> p _; exact: first_projection_continuous.
Qed.

(** Source for [affine_modular_translations]: "ker L|G = im tau is
    abelian, hence Delta_G|ker L = 1", Federer 2.7.16, p. 138. Direct
    formalisation, by abelian_normal_modular_unit. *)
Theorem affine_modular_translations (DG : AG -> R) :
  is_modular_function amul ainv DG -> forall p, affine_translations p -> DG p = 1.
Proof.
move=> hDG; apply: (abelian_normal_modular_unit hAG affine_translations_normal affine_translations_closed)=> //.
by move=> p q hp hq; exact: affine_group_translations_commute.
Qed.

(** Source for [affine_group_modular]: "If G is the affine group of
    R^n, then Delta_G(g) = |det L(g)|^{-1} whenever g in G", Federer
    2.7.16, p. 138, for the affine group of V and any modular function
    Delta_G of it (2.7.8, p. 126). Direct formalisation:
    (g, z) = (1_V, z)(g, 0), Delta_G(1_V, z) = 1 and
    Delta_G(g, 0) = |det g|^{-1}. *)
Theorem affine_group_modular (DG : AG -> R) :
  is_modular_function amul ainv DG -> forall p : AG, DG p = `|det p.1|^-1.
Proof.
move=> hDG [g z].
have [hM _] := modular_function_homomorphism hAG hDG.
have he : ((g, z) : AG) = amul (unit, z) (g, 0).
  rewrite /affine_group_mul /= (group_mul1g hgl).
  by rewrite (linear0 (hom_as_linear (set_val unit : Hom V V))) addr0.
rewrite [in LHS]he hM (affine_modular_translations hDG) // mul1r.
exact: (affine_modular_linear_part hDG g).
Qed.

End AffineModular.

Arguments affine_linear_character {R V B} hB {n b} hb p.
Arguments affine_translations {R V B} hB {n b} hb p.

Section EuclideanAffineModular.
Variable R : realType.
Variable n : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation E := (inner_metric_space hBn).
Local Notation GL := (set_type (linear_group hBn hbn)).
Local Notation AG := (GL * E)%type.
Local Notation A := (affine_group_action hBn hbn).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation Lam := (@euclidean_lebesgue_integral R n).

(** Source for [euclidean_lebesgue_affine_covariant_integral]: "L^n is
    |det o L|^{-1} covariant with respect to the usual action of G on
    R^n", Federer 2.7.16, p. 138, for the integral u |-> int u dL^n of
    2.7.1, p. 122. Direct formalisation. *)
Theorem euclidean_lebesgue_affine_covariant_integral :
  is_covariant_integral A (affine_linear_character hBn hbn) Lam.
Proof. exact: (affine_haar_integral_covariant hbn (euclidean_lebesgue_left_haar_integral R n)). Qed.

(** Source for [euclidean_lebesgue_affine_covariant]: "L^n is
    |det o L|^{-1} covariant with respect to the usual action of G on
    R^n", Federer 2.7.16, p. 138: L^n is a |det o L|^{-1} covariant
    measure over R^n in the sense of 2.7.1, p. 122. Direct
    formalisation. *)
Theorem euclidean_lebesgue_affine_covariant : is_covariant_measure A (affine_linear_character hBn hbn) Leb.
Proof.
exists Lam; split.
- exact: euclidean_lebesgue_integral_monotone.
- exact: (covariant_integral_law euclidean_lebesgue_affine_covariant_integral).
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_integral_represents.
- exact: euclidean_lebesgue_function_lattice_regular.
Qed.

(** Source for [euclidean_affine_group_modular]: "If G is the affine
    group of R^n, then Delta_G(g) = |det L(g)|^{-1} whenever g in G",
    Federer 2.7.16, p. 138. Direct formalisation for R^n with the inner
    product of 1.7.1, L(g, z) = g. *)
Corollary euclidean_affine_group_modular (DG : AG -> R) :
  is_modular_function (affine_group_mul hBn hbn) (affine_group_inv hBn hbn) DG ->
  forall p : AG, DG p = `|euclidean_det (hom_as_linear (set_val p.1 : Hom (R_n R n) (R_n R n)))|^-1.
Proof. by move=> hDG p; rewrite (affine_group_modular hDG p). Qed.

End EuclideanAffineModular.
