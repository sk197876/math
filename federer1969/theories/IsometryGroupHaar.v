(** Federer (1969), 2.7.16, printed p. 140, example (7): "Since L^n is G
    invariant and O(n) is compact, G is unimodular; furthermore we may apply
    2.7.10 to define a Haar integral lambda on K(G) by the formula lambda(u)
    = int theta_n^0(u) dL^n = int int u(tau_z o s) dtheta_n s dL^n z
    whenever u in K(G)." Here G is the isometry group of R^n
    (AffineGroupTopology.v, IsometryGroupStructure.v), acting on R^n by A(g,
    v) = g(v), with isotropy group G^0 = {tau_0 o s : s in O(n)}. The
    integral u |-> int u dL^n of 2.7.16, part (1), is a nonzero G invariant
    integral on K(R^n), and L^n is a G invariant measure. Unimodularity: by
    Weil's condition 2.7.11(1), p. 128, Delta_G agrees on G^0 with
    Delta_{G^0} = 1 (2.7.12, p. 129, G^0 being compact); Delta_G(tau_z) = 1
    follows from sigma o tau_z = tau_{-z} o sigma with sigma = -1_V in G^0
    and tau_z o tau_{-z} = 1_V, so Delta_G = 1. Federer does not give these
    steps. Haar integral: a left Haar integral Theta of O(n) is carried to a
    left Haar integral mu of G^0 by s |-> tau_0 o s; the map theta_n^0(u)(z)
    = Theta_s[u(tau_z o s)] is the map mu^0 of 2.7.10, pp. 127–128
    (is_coset_integral), and lambda = (int . dL^n) o mu^0 is a left Haar
    integral by 2.7.10(5), (6); it is a right Haar integral since G is
    unimodular. For theta_n the normalised Haar measure of O(n), Theta is
    the integral u |-> int u dtheta_n. The local erratum has no entry for p.
    140. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerNorm InnerMetric InnerNormedTopology LinearBasis TensorUP
  Bilinear Hom HomInner OrthogonalMaps FiniteCoordinates EuclideanInnerProduct GrassmannAbbreviations
  MeasureUP MeasurePushforward ProperMapUP RadonMeasureUP CompactSupportFunctionUP
  CompactSupportFunctionLattice FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP
  DaniellIntegralNegation FunctionLatticeRegularityUP RealIntegralFunctionalUP DaniellSpacePushforward DaniellSpaceCompactSpace
  SubtypeCompactHausdorff IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws HomeomorphismUP EquivariantPushforward
  CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP ModularFunctionUP ModularFunction
  UnimodularGroupUP UnimodularGroups CosetIntegralUP CosetIntegralLaws CosetIntegralExistence
  WeilCondition HomSpaceTopology LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation EuclideanLebesgueDimensions
  EuclideanAdditiveGroup EuclideanLebesgueTranslation EuclideanLebesgueHaar EuclideanLebesgueLinear AffineGroupTopology IsometryGroupStructure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactSpaceFunctions.
Variable R : realType.
Variable X : topologicalType.
Hypothesis hc : compact [set: X].

(** Source for [compact_space_continuous_compact]: every continuous
    real function on a compact space belongs to K(X), Federer 2.5.13,
    p. 106, as used for O(n) in 2.7.16, pp. 139–140. Supporting lemma. *)
Lemma compact_space_continuous_compact (f : X -> R) :
  continuous (f : X -> real_line_metric R) -> @compactly_supported_continuous_functions R X f.
Proof.
move=> hf; split=> //.
exact: (subclosed_compact (@real_function_support_closed R X _) hc (@subsetT _ _)).
Qed.

End CompactSpaceFunctions.

Section IsometryHaar.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation E := (inner_metric_space hBn).
Local Notation O := (orthogonal_group hBn hbn).
Local Notation G := (isometry_group hBn hbn).
Local Notation om := (@orthogonal_element_map R V _ hBn n _ hbn).
Local Notation A := (@isometry_point_action R V _ hBn n _ hbn).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation Lam := (@euclidean_lebesgue_integral R n).
Local Notation KE := (@compactly_supported_continuous_functions R E).
Local Notation KG := (@compactly_supported_continuous_functions R G).
Local Notation KO := (@compactly_supported_continuous_functions R O).

Variables (mulS : G -> G -> G) (invS : G -> G) (eS : G).
Hypothesis hS : is_subgroup_restriction (affine_group_mul hBn hbn) (affine_group_inv hBn hbn)
  (affine_group_unit hBn hbn) G mulS invS eS.
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn) (linear_group_inv hBn hbn)
  (linear_group_unit hBn hbn) O mulO invO eO.

(** Source for [hG]: the isometry group is a locally compact Hausdorff
    topological group, Federer 2.7.16, p. 140, used in this section. *)
Let hG : is_locally_compact_hausdorff_group mulS invS eS := isometry_group_lch hS.
(** Source for [hOl]: O(n) is a locally compact Hausdorff topological
    group, Federer 2.7.16, p. 139, used in this section. *)
Let hOl : is_locally_compact_hausdorff_group mulO invO eO := orthogonal_group_lch hO.
(** Source for [hOc]: O(n) is compact, Federer 2.7.16, p. 139, used in
    this section. *)
Let hOc : compact [set: O] := @orthogonal_group_compact_space R V _ hBn n _ hbn.
(** Source for [hA]: R^n is a homogeneous space of G, Federer 2.7.16,
    p. 140, used in this section. *)
Let hA : is_homogeneous_space mulS A := isometry_point_homogeneous hS hO.
(** Source for [hEH]: R^n is Hausdorff, used in this section. *)
Let hEH : hausdorff_space E := @inner_space_hausdorff R V _ hBn.
(** Source for [hEl]: R^n is locally compact, used in this section. *)
Let hEl : locally_compact [set: E] := @inner_space_locally_compact R V _ hBn n _ hbn.

(** Source for [isometry_map_homeomorphism]: an isometry g of R^n is a
    homeomorphism with inverse g^{-1}, Federer 2.7.16, p. 140.
    Supporting lemma. *)
Lemma isometry_map_homeomorphism (g : G) :
  is_homeomorphism_with_inverse (isometry_map g : E -> E) (isometry_map (invS g) : E -> E).
Proof.
have hc (h : G) : continuous (isometry_map h : E -> E).
  move=> v; apply: (@continuous_comp E (G * E)%type E (fun v : E => (h, v))
    (fun p : G * E => (isometry_map p.1 p.2 : E))).
    by apply: topological_pair_continuous; [exact: cst_continuous|move=> ?].
  exact: isometry_map_continuous.
have [h1 h2] := isometry_map_inv hS g.
by split; [exact: hc|exact: hc|exact: h1|exact: h2].
Qed.

(** Source for [isometry_lebesgue_preimage]: "L^n is G invariant",
    Federer 2.7.16, p. 140: L^n[g^{-1}(S)] = L^n(S) for every isometry
    g = tau_z o s, by the invariance of L^n under orthogonal maps and
    translations, 2.7.16, pp. 134–135. Direct formalisation. *)
Theorem isometry_lebesgue_preimage (g : G) (T : set E) : Leb ((isometry_map g : E -> E) @^-1` T) = Leb T.
Proof.
have he : (isometry_map g : E -> E) @^-1` T =
    (hom_as_linear (om (isometry_linear g)) : E -> E) @^-1` (euclidean_translation (isometry_translation g) @^-1` T).
  by apply/seteqP; split=> v.
rewrite he (euclidean_orthogonal_pushforward (orthogonal_element_orthogonal (isometry_linear g))).
exact: (congr1 (fun mu => mu T) (euclidean_lebesgue_translation_pushforward (isometry_translation g))).
Qed.

(** Source for [isometry_lebesgue_integral_invariant]: "L^n is G
    invariant", Federer 2.7.16, p. 140, for the integral:
    int u(g(v)) dL^n v = int u dL^n for u in K(R^n) and g in G.
    Supporting lemma, by 2.4.18 for the proper map g. *)
Lemma isometry_lebesgue_integral_invariant (g : G) (u : E -> R) : KE u -> Lam (u \o A g) = Lam u.
Proof.
move=> hu.
have hh := isometry_map_homeomorphism g.
have hf : continuous (isometry_map g : E -> E) := homeomorphism_continuous hh.
have hp : is_proper_map (isometry_map g : E -> E) := homeomorphism_with_inverse_proper hh.
have hpush := daniell_pushforward_integral hf hp (euclidean_lebesgue_is_measure R n)
  (@euclidean_lebesgue_integral_represents R n).
have he : measure_pushforward (isometry_map g : E -> E) Leb = Leb.
  by apply: funext=> T; exact: isometry_lebesgue_preimage.
rewrite he in hpush.
exact: (real_integral_functional_unique_on_lattice hpush (@euclidean_lebesgue_integral_represents R n) hu).
Qed.

(** Source for [isometry_lebesgue_integral_nonzero]: the integral
    u |-> int u dL^n does not vanish on K(R^n), since L^n is a Haar
    measure, Federer 2.7.16, p. 134. Supporting lemma. *)
Lemma isometry_lebesgue_integral_nonzero : exists2 u, KE u & Lam u <> 0.
Proof.
have [lam [hlH _ hrep _]] := @euclidean_lebesgue_left_haar R n.
have [u hu hu0] := nonzero_invariant_integral_nonzero hlH.
exists u=> //.
by rewrite (real_integral_functional_unique_on_lattice (@euclidean_lebesgue_integral_represents R n) hrep hu).
Qed.

(** Source for [isometry_lebesgue_invariant_integral]: "L^n is G
    invariant", Federer 2.7.16, p. 140, in the sense of 2.7.1, p. 122:
    u |-> int u dL^n is a nonzero G invariant integral on K(R^n).
    Direct formalisation. *)
Theorem isometry_lebesgue_invariant_integral : is_invariant_integral A Lam /\ exists2 u, KE u & Lam u <> 0.
Proof.
split; last exact: isometry_lebesgue_integral_nonzero.
split; first exact: (monotone_daniell_is_daniell (@euclidean_lebesgue_integral_monotone R n)).
by move=> u g hu; rewrite mul1r; exact: isometry_lebesgue_integral_invariant.
Qed.

(** Source for [isometry_lebesgue_invariant_measure]: "L^n is G
    invariant", Federer 2.7.16, p. 140: L^n is a G invariant measure over
    R^n in the sense of 2.7.1, p. 122. Direct formalisation. *)
Theorem isometry_lebesgue_invariant_measure : is_invariant_measure A Leb.
Proof.
exists Lam; split.
- exact: euclidean_lebesgue_integral_monotone.
- exact: (covariant_integral_law isometry_lebesgue_invariant_integral.1).
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_integral_represents.
- exact: euclidean_lebesgue_function_lattice_regular.
Qed.

Local Notation S0 := (isotropy_subgroup A 0).

(** Source for [isometry_isotropy_member]: tau_0 o s fixes 0, Federer
    2.7.16, p. 140, "G^0 = G cap {g : g(0) = 0} = O(n)". Supporting
    lemma. *)
Lemma isometry_isotropy_member (s : O) : S0 (isometry_of s 0).
Proof.
rewrite /isotropy_subgroup /= /A /isometry_point_action isometry_of_mapE add0r.
exact: (linear0 (hom_as_linear (om s))).
Qed.

(** Source for [isometry_isotropy_of]: the member tau_0 o s of G^0 for
    s in O(n), "G^0 = O(n)", Federer 2.7.16, p. 140. Definition. *)
Definition isometry_isotropy_of (s : O) : S0 := exist _ (isometry_of s 0) (mem_set (isometry_isotropy_member s)).

(** Source for [isometry_isotropy_translation]: the members of G^0 have
    translation part 0, Federer 2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_isotropy_translation (t : S0) : isometry_translation (set_val t) = 0.
Proof.
have h := set_valP t; rewrite /isotropy_subgroup /= /A /isometry_point_action in h.
by rewrite -isometry_map_zero; exact: h.
Qed.

(** Source for [isometry_isotropy_onto]: every member of G^0 is tau_0 o s
    with s = L(g) in O(n), "G^0 = O(n)", Federer 2.7.16, p. 140.
    Supporting lemma. *)
Lemma isometry_isotropy_onto (t : S0) : t = isometry_isotropy_of (isometry_linear (set_val t)).
Proof.
apply: val_inj=> /=.
transitivity (isometry_of (isometry_linear (set_val t)) (isometry_translation (set_val t))).
  exact: esym (isometry_ofK _).
by rewrite isometry_isotropy_translation.
Qed.

(** Source for [isometry_isotropy_of_continuous]: s |-> tau_0 o s is
    continuous from O(n) to G^0, Federer 2.7.16, p. 140. Supporting
    lemma. *)
Lemma isometry_isotropy_of_continuous : continuous isometry_isotropy_of.
Proof.
apply: set_type_continuous_into=> s.
apply: (@continuous_comp O (O * E)%type G (fun s : O => (s, (0 : E))) (fun p : O * E => isometry_of p.1 p.2)).
  by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
exact: isometry_of_continuous.
Qed.

(** Source for [isometry_isotropy_compact]: G^0 is compact, being the
    image of the compact group O(n), Federer 2.7.16, p. 140 ("O(n) is
    compact"). Supporting lemma. *)
Lemma isometry_isotropy_compact : compact [set: S0].
Proof.
have -> : [set: S0] = isometry_isotropy_of @` [set: O].
  apply/seteqP; split=> // t _; exists (isometry_linear (set_val t))=> //.
  exact: esym (isometry_isotropy_onto t).
apply: continuous_compact hOc; apply: continuous_subspaceT; exact: isometry_isotropy_of_continuous.
Qed.

(** Source for [isometry_isotropy_hausdorff]: G^0 is Hausdorff, Federer
    2.7.16, p. 140. Supporting lemma. *)
Lemma isometry_isotropy_hausdorff : hausdorff_space S0.
Proof. exact: set_type_hausdorff (lch_group_hausdorff hG). Qed.

(** Source for [isometry_isotropy_of_proper]: s |-> tau_0 o s is proper,
    Federer 2.2.17, p. 72, as needed for the image of a Haar integral
    of O(n) in 2.7.16, p. 140: O(n) is compact and G^0 Hausdorff.
    Supporting lemma. *)
Lemma isometry_isotropy_of_proper : is_proper_map isometry_isotropy_of.
Proof.
move=> C hC; apply: (subclosed_compact _ hOc (@subsetT _ _)).
apply: preimage_closed; last exact: compact_closed isometry_isotropy_hausdorff hC.
by move=> s _; exact: isometry_isotropy_of_continuous.
Qed.

(** Source for [isometry_isotropy_linear_continuous]: t |-> L(t) is
    continuous from G^0 to O(n), Federer 2.7.16, p. 140. Supporting
    lemma. *)
Lemma isometry_isotropy_linear_continuous : continuous (fun t : S0 => isometry_linear (set_val t)).
Proof.
move=> t; apply: (@continuous_comp S0 G O set_val isometry_linear).
  exact: set_type_val_continuous.
exact: isometry_linear_continuous.
Qed.

(** Source for [negation_linear]: the linear map -1_V of R^n,
    supporting the unimodularity of G, Federer 2.7.16, p. 140.
    Definition. *)
Definition negation_linear : {linear V -> V} := GRing.Linear.clone _ _ _ _ (@GRing.opp V) _.

(** Source for [negation_linear_orthogonal]: -1_V is orthogonal,
    Federer 1.7.2, p. 28. Supporting lemma. *)
Lemma negation_linear_orthogonal : is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n)
  negation_linear.
Proof.
move=> x y; rewrite /negation_linear /=.
rewrite -[- x]scaleN1r -[- y]scaleN1r (bilZl (inner_bilinear hBn)) (bilZr (inner_bilinear hBn)).
by rewrite !scaleN1r opprK.
Qed.

(** Source for [isometry_antipodal]: -1_V as a member of O(n),
    supporting the unimodularity of G, Federer 2.7.16, p. 140.
    Definition. *)
Definition isometry_antipodal : O := orthogonal_element_of hBn hbn negation_linear_orthogonal.

Section Isotropy.
Variables (mul0 : S0 -> S0 -> S0) (inv0 : S0 -> S0) (e0 : S0).
Hypothesis h0 : is_subgroup_restriction mulS invS eS S0 mul0 inv0 e0.

(** Source for [hl0]: G^0 is a locally compact Hausdorff topological
    group, Federer 2.7.10, p. 127, used in this section. *)
Let hl0 : is_locally_compact_hausdorff_group mul0 inv0 e0.
Proof.
apply: (subgroup_restriction_locally_compact_hausdorff h0 hG).
exact: (isotropy_subgroup_closed hA hEH).
Qed.

(** Source for [isometry_isotropy_of_mul]: s |-> tau_0 o s is a
    homomorphism of O(n) into G^0, "G^0 = O(n)", Federer 2.7.16,
    p. 140. Supporting lemma. *)
Lemma isometry_isotropy_of_mul (s t : O) :
  mul0 (isometry_isotropy_of s) (isometry_isotropy_of t) = isometry_isotropy_of (mulO s t).
Proof.
apply: val_inj; rewrite /= -!set_valE (subgroup_restriction_mul h0) /=.
rewrite (isometry_of_mul hS hO) add0r.
by rewrite (linear0 (hom_as_linear (om s))).
Qed.

(** Source for [isometry_unimodular_isotropy]: Delta_G = 1 on G^0,
    Federer 2.7.16, p. 140, "since L^n is G invariant and O(n) is
    compact": Weil's condition 2.7.11(1), p. 128, for the nonzero
    invariant integral int . dL^n gives Delta_G = Delta_{G^0} on G^0,
    and Delta_{G^0} = 1 because G^0 is compact (2.7.12, p. 129).
    Supporting lemma. *)
Lemma isometry_unimodular_isotropy (DG : G -> R) :
  is_modular_function mulS invS DG -> forall t : S0, DG (set_val t) = 1.
Proof.
move=> hDG t.
have [DS hDS] := modular_function_exists R hl0.
have hchiM (g h : G) : (fun _ => 1 : R) (mulS g h) = (fun _ => 1 : R) g * (fun _ => 1 : R) h.
  by rewrite mulr1.
have hchi0 (g : G) : (fun _ => 1 : R) g != 0 by exact: oner_neq0.
have hchic : continuous ((fun _ => 1) : G -> real_line_metric R) by exact: cst_continuous.
have [hnu hnz] := isometry_lebesgue_invariant_integral.
have hW := weil_condition_necessary hG hA hEH h0 hDG hDS hchiM hchi0 hchic hnu hnz.
have hDS1 := (unimodular_iff_modular_unit hl0 hDS).1 (compact_group_unimodular hl0 isometry_isotropy_compact).
by rewrite -(hW t) hDS1 mulr1.
Qed.


(** Source for [isotropy_transport]: the left Haar integral of G^0
    corresponding to a left Haar integral Theta of O(n) under
    s |-> tau_0 o s, "G^0 = O(n)", Federer 2.7.16, p. 140:
    f |-> Theta(f o (s |-> tau_0 o s)). Definition. *)
Definition isotropy_transport (Theta : (O -> R) -> R) : (S0 -> R) -> R :=
  fun f => Theta (f \o isometry_isotropy_of).

(** Source for [isotropy_transport_haar]: the image of a left Haar
    integral of O(n) under s |-> tau_0 o s is a left Haar integral of
    G^0, Federer 2.7.16, p. 140, with 2.5.19, p. 113. Supporting lemma:
    s |-> tau_0 o s is a continuous proper isomorphism onto G^0. *)
Lemma isotropy_transport_haar (Theta : (O -> R) -> R) :
  is_left_haar_integral mulO Theta -> is_left_haar_integral mul0 (isotropy_transport Theta).
Proof.
move=> [[hD hlaw] hM [u hu hu0]].
have hc := isometry_isotropy_of_continuous; have hp := isometry_isotropy_of_proper.
split.
- split; first exact: (daniell_pushforward_daniell hc hp hD).
  move=> f h hf; rewrite mul1r /isotropy_transport.
  have hfc := compactly_supported_compose hc hp hf.
  rewrite -[RHS](mul1r) -(hlaw _ (isometry_linear (set_val h)) hfc); congr Theta.
  apply: funext=> s; rewrite /= /left_multiplication_action.
  by rewrite {1}(isometry_isotropy_onto h) isometry_isotropy_of_mul.
- exact: (daniell_pushforward_monotone hc hp hM).
- exists (u \o (fun t : S0 => isometry_linear (set_val t))).
    apply: (compact_space_continuous_compact isometry_isotropy_compact)=> t.
    apply: continuous_comp; first exact: isometry_isotropy_linear_continuous.
    exact: hu.1.
  rewrite /isotropy_transport.
  have -> : (u \o (fun t : S0 => isometry_linear (set_val t))) \o isometry_isotropy_of = u.
    by apply: funext=> s; rewrite /= isometry_of_linear.
  exact: hu0.
Qed.

(** Source for [isometry_coset_map]: theta_n^0(u)(z) = int u(tau_z o s)
    dtheta_n s, Federer 2.7.16, p. 140, for a left Haar integral Theta
    of O(n) in place of int . dtheta_n. Definition. *)
Definition isometry_coset_map (Theta : (O -> R) -> R) (u : G -> R) (z : E) : R :=
  Theta (fun s => u (isometry_of s z)).

(** Source for [isometry_coset_section_compact]: s |-> u(tau_z o s)
    belongs to K(O(n)) for every continuous u on G, Federer 2.7.16,
    p. 140. Supporting lemma. *)
Lemma isometry_coset_section_compact (u : G -> R) (z : E) :
  continuous (u : G -> real_line_metric R) -> KO (fun s => u (isometry_of s z)).
Proof.
move=> hu; apply: (compact_space_continuous_compact hOc)=> s.
apply: (@continuous_comp O G (real_line_metric R) (fun s => isometry_of s z) u); last exact: hu.
apply: (@continuous_comp O (O * E)%type G (fun s : O => (s, z)) (fun p : O * E => isometry_of p.1 p.2)).
  by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
exact: isometry_of_continuous.
Qed.

(** Source for [isometry_coset_integral]: "theta_n^0" in Federer
    2.7.16, p. 140, is the map mu^0 of 2.7.10, pp. 127–128, for the
    left Haar integral mu of G^0 corresponding to Theta:
    theta_n^0(u)(g 0) = mu_t[u(g t)]. Direct formalisation; the left
    invariance of Theta gives Theta_s[u(tau_z o L(g) o s)] =
    Theta_s[u(tau_z o s)]. *)
Theorem isometry_coset_integral (Theta : (O -> R) -> R) :
  is_left_haar_integral mulO Theta ->
  is_coset_integral mulS A 0 (isotropy_transport Theta) (isometry_coset_map Theta).
Proof.
move=> hT; have hmu := isotropy_transport_haar hT.
have [[_ hlaw] _ _] := hT.
have [M hM] := coset_integral_exists hG hA hEH h0 hmu.
have hval u g : KG u -> isometry_coset_map Theta u (A g 0) =
    isotropy_transport Theta (fun t : S0 => u (mulS g (set_val t))).
  move=> hu; rewrite /isometry_coset_map /isotropy_transport /A /isometry_point_action isometry_map_zero.
  have hw := isometry_coset_section_compact (isometry_translation g) hu.1.
  rewrite -[LHS]mul1r -(hlaw _ (isometry_linear g) hw); congr Theta.
  apply: funext=> s; rewrite /= /left_multiplication_action.
  have -> : mulS g (isometry_of s 0) = isometry_of (mulO (isometry_linear g) s) (isometry_translation g).
    rewrite -[in LHS](isometry_ofK g) (isometry_of_mul hS hO).
    by rewrite (linear0 (hom_as_linear (om (isometry_linear g)))) addr0.
  by [].
split.
- move=> u hu; have -> : isometry_coset_map Theta u = M u.
    apply: funext=> z; have hz : A (isometry_of eO z) 0 = z.
      by rewrite /A /isometry_point_action isometry_map_zero.
    by rewrite -{1 2}hz hval // (coset_integral_value hM).
  exact: (coset_integral_compact hM hu).
- by move=> u g hu; exact: hval.
Qed.

End Isotropy.

(** Source for [isometry_group_unimodular]: "Since L^n is G invariant
    and O(n) is compact, G is unimodular", Federer 2.7.16, p. 140.
    Direct formalisation (2.7.12, p. 129). Delta_G = 1 on G^0 by
    isometry_unimodular_isotropy; for sigma = -1_V and tau_z,
    sigma o tau_z = tau_{-z} o sigma and tau_z o tau_{-z} = 1_V give
    Delta_G(tau_z)^2 = 1; and g = tau_{g(0)} o (tau_0 o L(g)). These
    steps are supplied. *)
Theorem isometry_group_unimodular : is_unimodular R mulS invS.
Proof.
have [mul0 [inv0 [e0 [h0 _]]]] := isotropy_group_exists (0 : E) hG hA hEH.
have [DG hDG] := modular_function_exists R hG.
have [hDM hDe] := modular_function_homomorphism hG hDG.
have hD0 (s : O) : DG (isometry_of s 0) = 1.
  exact: (isometry_unimodular_isotropy h0 hDG (isometry_isotropy_of s)).
have hneg x : om isometry_antipodal x = - x by [].
have hunit x : om eO x = x := orthogonal_element_unit hO x.
pose tau z := isometry_of eO z.
have hT z : DG (tau z) = 1.
  pose sigma := isometry_of isometry_antipodal 0.
  have h1 : mulS sigma (tau z) = mulS (tau (- z)) sigma.
    apply: (isometry_ext)=> v; rewrite !(isometry_map_mul hS) !isometry_of_mapE !hneg !hunit.
    by rewrite !add0r opprD.
  have h2 : mulS (tau z) (tau (- z)) = eS.
    apply: (isometry_ext)=> v; rewrite (isometry_map_mul hS) (isometry_map_unit hS) !isometry_of_mapE !hunit.
    by rewrite addrA subrr add0r.
  have e1 := congr1 DG h1; rewrite !hDM (hD0 isometry_antipodal) mul1r mulr1 in e1.
  have e2 := congr1 DG h2; rewrite hDM -e1 hDe in e2.
  have hpos := modular_function_positive hDG (tau z).
  have /orP [/eqP h|/eqP h] : (DG (tau z) == 1) || (DG (tau z) == -1).
    by rewrite -sqrf_eq1 expr2 e2.
  - exact: h.
  - by move: hpos; rewrite h ltr0N1.
apply/(unimodular_iff_modular_unit hG hDG)=> g.
have he : g = mulS (tau (isometry_translation g)) (isometry_of (isometry_linear g) 0).
  apply: isometry_ext=> v; rewrite (isometry_map_mul hS) !isometry_of_mapE hunit add0r.
  by [].
by rewrite he hDM hT hD0 mulr1.
Qed.

(** Source for [isometry_haar_integral]: "we may apply 2.7.10 to define
    a Haar integral lambda on K(G) by the formula lambda(u) =
    int theta_n^0(u) dL^n = int int u(tau_z o s) dtheta_n s dL^n z",
    Federer 2.7.16, p. 140, for every left Haar integral Theta of O(n)
    in place of int . dtheta_n: lambda is a left and a right Haar
    integral of G. Direct formalisation, by 2.7.10(5), (6) and the
    unimodularity of G. *)
Theorem isometry_haar_integral (Theta : (O -> R) -> R) :
  is_left_haar_integral mulO Theta ->
  is_left_haar_integral mulS (fun u => Lam (isometry_coset_map Theta u)) /\
  is_right_haar_integral mulS invS (fun u => Lam (isometry_coset_map Theta u)).
Proof.
move=> hT.
have [mul0 [inv0 [e0 [h0 _]]]] := isotropy_group_exists (0 : E) hG hA hEH.
have hM := isometry_coset_integral h0 hT.
have hmu := isotropy_transport_haar h0 hT.
have [hLi hLn] := isometry_lebesgue_invariant_integral.
have hLD := covariant_integral_daniell hLi.
have hl : is_left_haar_integral mulS (fun u => Lam (isometry_coset_map Theta u)).
  split.
  - exact: ((coset_integral_covariant hG hA hEH h0 hmu hM (fun _ => 1) hLD).1 hLi).
  - exact: (coset_integral_monotone_daniell hG hA hEH hmu hM (@euclidean_lebesgue_integral_monotone R n)).
  - have [v hv hv0] := hLn.
    have [u hu hMu] := coset_integral_onto hG hA hEH h0 hmu hM hv.
    by exists u=> //; rewrite hMu.
by split=> //; exact: (isometry_group_unimodular _).1 hl.
Qed.

(** Source for [isometry_haar_integral_theta]: Federer 2.7.16, p. 140,
    with theta_n the normalised Haar measure of O(n) (example (6),
    p. 139): there is a left Haar integral Theta of O(n) represented by
    theta_n, so that Theta(f) = int f dtheta_n for f in K(O(n)); the
    formula lambda(u) = int int u(tau_z o s) dtheta_n s dL^n z defines a
    left and right Haar integral of G, and theta_n^0 is the map mu^0 of
    2.7.10; the value of lambda on K(G) does not depend on the choice of
    Theta represented by theta_n. Direct formalisation. *)
Theorem isometry_haar_integral_theta (theta : set O -> \bar R) :
  is_normalised_haar_measure mulO theta ->
  exists Theta : (O -> R) -> R,
    [/\ is_left_haar_integral mulO Theta, is_real_integral_functional theta KO Theta,
      is_left_haar_integral mulS (fun u => Lam (isometry_coset_map Theta u)),
      is_right_haar_integral mulS invS (fun u => Lam (isometry_coset_map Theta u)) &
      forall Theta', is_real_integral_functional theta KO Theta' ->
        forall u, KG u -> Lam (isometry_coset_map Theta' u) = Lam (isometry_coset_map Theta u)].
Proof.
move=> [[Theta [hT _ hrep _]] _].
have [hl hr] := isometry_haar_integral hT.
exists Theta; split=> // Theta' hrep' u hu; congr Lam; apply: funext=> z.
apply: (real_integral_functional_unique_on_lattice hrep' hrep).
exact: isometry_coset_section_compact hu.1.
Qed.

End IsometryHaar.
