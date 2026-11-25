(** Federer (1969), 2.7.16, printed pp. 140–141, example (7): "If X is the
    space of all m dimensional affine subspaces of R^n, and p in O*(n, n -
    m), then a G invariant integral mu on K(X) is given by the formula mu(v)
    = int int v[s(p^{-1}{y})] dtheta_n s dL^{n-m} y whenever v in K(X). ...
    we see that xi is continuous and open, im xi = X, delta is continuous,
    xi is proper, hence gamma = xi_#(theta_n x L^{n-m}) is a Radon measure
    over X. Then we use the fact that t xi(s, y) = xi(t s, y), tau_z xi(s,
    y) = xi(s, y + (p o s^{-1}) z) ... to verify that gamma is invariant
    under the action of G. Since s[p^{-1}{y}] = (p s^{-1})^{-1}{y} for s in
    O(n), y in R^n, and the function mapping s onto p s^{-1} carries theta_n
    onto theta*_{n,n-m} [see (6)], we obtain the alternate formula mu(v) =
    int int v(q^{-1}{y}) dtheta*_{n,n-m} q dL^{n-m} y." Here theta_n is a
    normalised Haar measure of O(n) (example (6)), Theta a left Haar
    integral of O(n) represented by theta_n, so that Theta(f) = int f
    dtheta_n for f in K(O(n)), and L^{n-m} with its integral u |-> int u
    dL^{n-m} of 2.7.16, part (1). The product measure theta_n x L^{n-m} of
    2.6.1 is a Radon measure (CompactProductRadon.v), so gamma is a Radon
    measure by 2.2.17, p. 72; gamma represents mu by 2.4.18, p. 90, and
    2.6.4, p. 119. The invariance of mu under rotations tau_0 o t follows
    from the left invariance of Theta; under translations tau_z from
    Fubini's theorem (2.6.2, 2.6.4) and the translation invariance of
    L^{n-m}; every isometry is tau_z o t. That gamma is the K(X) regular
    measure of mu, as an invariant measure in the sense of 2.7.1, p. 122,
    follows from 2.7.15, p. 133 (X is a countable union of compact sets) and
    the uniqueness of Radon measures representing an integral. The local
    erratum has no entry for pp. 140–141. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground InnerProductUP InnerProductLaws InnerNorm InnerMetric
  InnerNormedTopology LinearBasis Bilinear TensorUP Hom HomInner ModuleQuotient GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps ProperMapUP
  MeasureUP MeasurePushforward BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity
  RadonProperPushforward ProductMeasure CompactSupportFunctionUP CompactSupportFunctionLattice
  FunctionLatticeUP DaniellIntegralUP MonotoneDaniellIntegralUP DaniellIntegralNegation
  FunctionLatticeRegularityUP RealIntegralFunctionalUP DaniellSpacePushforward DaniellProductUP
  DaniellProductMonotone CompactProductSections CompactDaniellIterationCommutation
  IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws HomeomorphismUP CovariantIntegralUP CovariantIntegralLaws
  HaarIntegralUP HaarIntegralLaws CovariantMeasureRadon HomogeneousCovariantMeasureRadon
  HomSpaceTopology LinearGroupTopology LinearGroupSealed OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure CompactGroupHaarNormalisation CompactGroupHomogeneousMeasures
  OrthogonalInjectionSpaces GrassmannHomogeneousSpace CosetIntegralExistence
  EuclideanLebesgueDimensions EuclideanAdditiveGroup TranslationInvariantHaar EuclideanLebesgueHaar
  CountableOpenBaseUP AffineGroupTopology IsometryGroupStructure IsometryGroupHaar CompactProductRadon
  AffineSubspaceSpace
  OrthogonalProjectionFibres AffineSubspaceParametrisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InvariantMeasure.
Variable R : realType.
Variables n m : nat.
Hypothesis hmn : (m <= n)%N.
Local Notation k := (n - m)%N.
Local Notation Vn := (R_n R n).
Local Notation Vk := (R_n R k).
Local Notation Vm := (R_n R m).
Local Notation Bn := (@euclidean_inner_product R n).
Local Notation Bk := (@euclidean_inner_product R k).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hBk := (@euclidean_inner_productP R k).
Local Notation hBm := (@euclidean_inner_productP R m).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation hbk := (@coordinate_basisP R k).
Local Notation hbm := (@coordinate_basisP R m).
Local Notation E := (inner_metric_space hBn).
Local Notation HVV := (inner_metric_space (hom_inner_productP hBn hBn hbn)).
Local Notation Ek := (inner_metric_space hBk).
Local Notation X := (affine_subspace_space hBm hBn hbm hbn).
Local Notation O := (orthogonal_group hBn hbn).
Local Notation G := (isometry_group hBn hbn).
Local Notation OP := (set_type (orthogonal_projections hBk hBn hbn)).
Local Notation pm := (@orthogonal_projection_map R Vk Vn Bk Bn hBk hBn n _ hbn).
Local Notation om := (@orthogonal_element_map R Vn Bn hBn n _ hbn).
Local Notation Aact := (affine_subspace_action hBm hBn hbm hbn).
Local Notation fibre := (projection_fibre hmn).
Local Notation Lk := (@euclidean_lebesgue_measure R k).
Local Notation Lamk := (@euclidean_lebesgue_integral R k).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KO := (@compactly_supported_continuous_functions R O).
Local Notation KEk := (@compactly_supported_continuous_functions R Ek).
Local Notation KOE := (@compactly_supported_continuous_functions R (O * Ek)%type).
Local Notation KOP := (@compactly_supported_continuous_functions R OP).

Variables (mulS : G -> G -> G) (invS : G -> G) (eS : G).
Hypothesis hS : is_subgroup_restriction (affine_group_mul hBn hbn) (affine_group_inv hBn hbn)
  (affine_group_unit hBn hbn) G mulS invS eS.
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn) (linear_group_inv hBn hbn)
  (linear_group_unit hBn hbn) O mulO invO eO.
Variable p : OP.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Variable Theta : (O -> R) -> R.
Hypothesis hT : is_left_haar_integral mulO Theta.
Hypothesis hTrep : is_real_integral_functional theta KO Theta.

Local Notation xi := (affine_parametrisation hmn p).

(** Source for [hOl]: O(n) is a locally compact Hausdorff group, used
    in this section. *)
Let hOl : is_locally_compact_hausdorff_group mulO invO eO := orthogonal_group_lch hO.
(** Source for [hOc]: O(n) is compact, used in this section. *)
Let hOc : compact [set: O] := @orthogonal_group_compact_space R Vn Bn hBn n _ hbn.
(** Source for [hOH]: O(n) is Hausdorff, used in this section. *)
Let hOH : hausdorff_space O := lch_group_hausdorff hOl.
(** Source for [hOL]: O(n) is locally compact, used in this section. *)
Let hOL : locally_compact [set: O] := lch_group_locally_compact hOl.
(** Source for [hEkH]: R^{n-m} is Hausdorff, used in this section. *)
Let hEkH : hausdorff_space Ek := @inner_space_hausdorff R Vk Bk hBk.
(** Source for [hEkl]: R^{n-m} is locally compact, used in this
    section. *)
Let hEkl : locally_compact [set: Ek] := @inner_space_locally_compact R Vk Bk hBk k _ hbk.
(** Source for [hG]: G is a locally compact Hausdorff group, used in
    this section. *)
Let hG : is_locally_compact_hausdorff_group mulS invS eS := isometry_group_lch hS.
(** Source for [hXA]: X is a homogeneous space of G, used in this
    section. *)
Let hXA : is_homogeneous_space mulS Aact := affine_subspace_homogeneous hBm hbm hS hO.
(** Source for [hXH]: X is Hausdorff, used in this section. *)
Let hXH : hausdorff_space X := @affine_subspace_space_hausdorff R Vm Vn _ _ hBm hBn m _ n _ hbm hbn.
(** Source for [hXl]: X is locally compact, used in this section. *)
Let hXl : locally_compact [set: X] := affine_subspace_space_locally_compact hS hO.
(** Source for [hxic]: xi is continuous, used in this section. *)
Let hxic : continuous xi := @affine_parametrisation_continuous R n m hmn _ _ _ hO p.
(** Source for [hxip]: xi is proper, used in this section. *)
Let hxip : is_proper_map xi := @affine_parametrisation_proper R n m hmn _ _ _ hO p.
(** Source for [hTm]: Theta is a monotone Daniell integral, used in this
    section. *)
Let hTm : is_monotone_daniell_integral KO Theta := nonzero_invariant_integral_monotone hT.
(** Source for [hTD]: Theta is a Daniell integral, used in this
    section. *)
Let hTD : is_daniell_integral KO Theta := monotone_daniell_is_daniell hTm.
(** Source for [hLm]: the integral of L^{n-m} is a monotone Daniell
    integral, used in this section. *)
Let hLm : is_monotone_daniell_integral KEk Lamk := @euclidean_lebesgue_integral_monotone R k.
(** Source for [hLD]: the integral of L^{n-m} is a Daniell integral,
    used in this section. *)
Let hLD : is_daniell_integral KEk Lamk := monotone_daniell_is_daniell hLm.
(** Source for [hthm]: theta_n is a measure, used in this section. *)
Let hthm : is_measure theta.
Proof. by have [[Th [_ hm _ _]] _] := htheta. Qed.
(** Source for [hLkm]: L^{n-m} is a measure, used in this section. *)
Let hLkm : is_measure Lk := euclidean_lebesgue_is_measure R k.

(** Source for [htheta_radon]: theta_n is a Radon measure, by 2.7.14,
    p. 131 (O(n) is compact), used in this section. *)
Let htheta_radon : is_radon_measure theta.
Proof.
have [hl _] := htheta.
apply: (left_covariant_measure_radon hOl (chi := fun _ => 1)); last first.
  by right; exists (fun _ => [set: O]); split=> // y _; exists 0%N.
exact: nonzero_invariant_measure_invariant hl.
Qed.

(** Source for [affine_product_measure]: the cartesian product
    theta_n x L^{n-m} of 2.6.1, p. 114, over O(n) x R^{n-m}, Federer
    2.7.16, p. 141. Definition. *)
Definition affine_product_measure : set (O * Ek) -> \bar R := product_measure hthm hLkm.

(** Source for [affine_invariant_measure]: gamma = xi_#(theta_n x
    L^{n-m}), the image measure of 2.1.2, p. 54, Federer 2.7.16,
    p. 141. Definition. *)
Definition affine_invariant_measure : set X -> \bar R := measure_pushforward xi affine_product_measure.

(** Source for [affine_invariant_integral]: mu(v) = int int
    v[s(p^{-1}{y})] dtheta_n s dL^{n-m} y, Federer 2.7.16, p. 140, with
    Theta for int . dtheta_n. Definition. *)
Definition affine_invariant_integral (v : X -> R) : R := Lamk (fun y => Theta (fun s => v (xi (s, y)))).

(** Source for [hcover]: R^{n-m} is covered by the open balls of radius
    k, each with compact closure, used in this section. *)
Let hcover := @euclidean_ball_cover R k.

(** Source for [hball_increasing]: the balls {y : |y| < j} increase
    with j, used in this section. *)
Let hball_increasing : forall i j, (i <= j)%N ->
  @euclidean_open_ball_sequence R k i `<=` @euclidean_open_ball_sequence R k j.
Proof.
move=> i j hij y; rewrite /euclidean_open_ball_sequence /= => hy.
by apply: lt_le_trans hy _; rewrite ler_nat.
Qed.

(** Source for [orthogonal_group_countable_base]: O(n) has a countable
    base, supporting the Radon property of theta_n x L^{n-m} in Federer
    2.7.16, p. 141: the traces on O(n) of a countable relative base of
    the compact subset O(n) of the metric space Hom(R^n, R^n)
    (compact_subset_relative_base). Supporting lemma. *)
Lemma orthogonal_group_countable_base : exists U : nat -> set O, is_countable_open_base U.
Proof.
have [U [hUo hU]] := compact_subset_relative_base (@orthogonal_maps_compact R Vn Bn hBn n _ hbn).
exists (fun j => if j is j'.+1 then (fun s : O => (om s : HVV)) @^-1` U j' else set0); constructor.
- move=> [|j]; first exact: open0.
  apply: open_comp (hUo j)=> s _; exact: orthogonal_element_continuous.
- by [].
- move=> W [W1 [W2 hW2 <-] <-] s hs.
  have [i [hi hiW]] := hU W2 hW2 (om s) (orthogonal_element_orthogonal s) hs.
  by exists i.+1; split=> // t ht; exact: hiW.
Qed.

(** Source for [affine_product_measure_radon]: theta_n x L^{n-m} is a
    Radon measure over O(n) x R^{n-m}, presupposed in Federer 2.7.16,
    p. 141. Supporting lemma, by compact_product_measure_radon. *)
Lemma affine_product_measure_radon : is_radon_measure affine_product_measure.
Proof.
have [U hU] := orthogonal_group_countable_base.
have [V hV] := @euclidean_countable_open_base R k.
have [hWo hWc hWT] := hcover.
exact: (compact_product_measure_radon (A := Theta) (B := Lamk) hthm hLkm hOH hOc hEkH hEkl hU hV
  hWo hWc hball_increasing hWT (radon_borel_regular hthm htheta_radon) (@euclidean_lebesgue_borel_regular R k)
  hTm hLm hTrep (@euclidean_lebesgue_integral_represents R k)).
Qed.

(** Source for [affine_product_measure_represents]: theta_n x L^{n-m}
    represents the iterated integral on K(O(n) x R^{n-m}), Federer
    2.6.4, p. 119, as corrected in the erratum, p. 2, used in 2.7.16,
    p. 141. Supporting lemma. *)
Lemma affine_product_measure_represents :
  is_real_integral_functional affine_product_measure KOE (fun h => Lamk (fun y => Theta (fun s => h (s, y)))).
Proof.
exact: (compact_product_measure_represents hthm hLkm hOH hOc hEkH hEkl hTm hLm hTrep
  (@euclidean_lebesgue_integral_represents R k)).
Qed.

(** Source for [affine_invariant_measure_radon]: "xi is proper, hence
    gamma = xi_#(theta_n x L^{n-m}) is a Radon measure over X", Federer
    2.7.16, p. 141. Direct formalisation, by 2.2.17, p. 72. *)
Theorem affine_invariant_measure_radon : is_radon_measure affine_invariant_measure.
Proof.
exact: (proper_continuous_radon_pushforward (product_measure_is_measure hthm hLkm)
  affine_product_measure_radon hXH hXl hxic hxip).
Qed.

(** Source for [affine_invariant_measure_is_measure]: gamma is a
    measure, Federer 2.1.2, p. 54. Supporting lemma. *)
Lemma affine_invariant_measure_is_measure : is_measure affine_invariant_measure.
Proof. exact: measure_pushforward_is_measure (product_measure_is_measure hthm hLkm). Qed.

(** Source for [affine_iterated_product]: the iterated integral
    h |-> int int h(s, y) dtheta_n s dL^{n-m} y is the product
    Daniell integral, Federer 2.6.4, p. 119. Supporting lemma. *)
Lemma affine_iterated_product :
  is_daniell_product Theta Lamk (fun h : O * Ek -> R => Lamk (fun y => Theta (fun s => h (s, y)))).
Proof. exact: (compact_product_iterated_daniell_product hOH hOc hEkH hEkl hTm hLm). Qed.

(** Source for [affine_invariant_integral_monotone]: mu is a monotone
    Daniell integral on K(X), Federer 2.7.16, p. 140, as the image
    xi_*(theta_n x L^{n-m}) of 2.5.19, p. 113. Supporting lemma. *)
Lemma affine_invariant_integral_monotone : is_monotone_daniell_integral KX affine_invariant_integral.
Proof.
have hCm := daniell_product_is_monotone hOH hOL hEkH hEkl hTm hLm affine_iterated_product.
exact: (daniell_pushforward_monotone hxic hxip hCm).
Qed.

(** Source for [affine_invariant_measure_represents]: gamma represents
    mu on K(X): int v dgamma = int int v[s(p^{-1}{y})] dtheta_n s
    dL^{n-m} y, Federer 2.7.16, pp. 140–141, by 2.4.18, p. 90.
    Direct formalisation. *)
Theorem affine_invariant_measure_represents :
  is_real_integral_functional affine_invariant_measure KX affine_invariant_integral.
Proof.
exact: (daniell_pushforward_integral hxic hxip (product_measure_is_measure hthm hLkm)
  affine_product_measure_represents).
Qed.

(** Source for [affine_section_rotation]: s |-> v(xi(s, y)) belongs to
    K(O(n)) for v in K(X), Federer 2.7.16, p. 141. Supporting lemma. *)
Lemma affine_section_rotation (v : X -> R) (y : Ek) : KX v -> KO (fun s => v (xi (s, y))).
Proof.
move=> hv; have hh := compactly_supported_compose hxic hxip hv.
exact: (compact_product_first_section y hOH hh).
Qed.

(** Source for [affine_section_translation]: y |-> v(xi(s, y)) belongs
    to K(R^{n-m}) for v in K(X), Federer 2.7.16, p. 141. Supporting
    lemma. *)
Lemma affine_section_translation (v : X -> R) (s : O) : KX v -> KEk (fun y => v (xi (s, y))).
Proof.
move=> hv; have hh := compactly_supported_compose hxic hxip hv.
exact: (compact_product_second_section s hEkH hh).
Qed.

(** Source for [affine_invariant_integral_rotation]: mu(v o A_t) = mu(v)
    for the rotations t in O(n), Federer 2.7.16, p. 141, from
    t xi(s, y) = xi(t s, y) and the left invariance of theta_n.
    Supporting lemma. *)
Lemma affine_invariant_integral_rotation (v : X -> R) (t : O) :
  KX v -> affine_invariant_integral (v \o Aact (isometry_of t 0)) = affine_invariant_integral v.
Proof.
move=> hv; have [[_ hlaw] _ _] := hT.
rewrite /affine_invariant_integral; apply: (congr1 Lamk); apply: funext=> y.
rewrite -[RHS]mul1r -(hlaw _ t (affine_section_rotation y hv)); apply: (congr1 Theta).
apply: funext=> s; change (v (Aact (isometry_of t 0) (xi (s, y))) = v (xi (mulO t s, y))).
by rewrite (affine_parametrisation_rotate hmn hO).
Qed.

(** Source for [lebesgue_integral_shift]: int u(y + c) dL^{n-m} y =
    int u dL^{n-m} for u in K(R^{n-m}), Federer 2.7.16, p. 135.
    Supporting lemma. *)
Lemma lebesgue_integral_shift (u : Ek -> R) (c : Ek) : KEk u -> Lamk (fun y => u (y + c)) = Lamk u.
Proof.
move=> hu.
have h := @invariant_borel_integral_translation R Ek _ _ _ (euclidean_additive_lch_group R k) Lk
  (euclidean_lebesgue_invariant_borel R k) u c hu.
have -> : (fun y => u (y + c)) = u \o (fun y => c + y) by apply: funext=> y; rewrite /= addrC.
exact: h.
Qed.

(** Source for [affine_invariant_integral_translation]: mu(v o A_tau) =
    mu(v) for the translations tau_z, Federer 2.7.16, p. 141, from
    tau_z xi(s, y) = xi(s, y + (p o s^{-1}) z), Fubini's theorem
    (2.6.4, p. 119) and the translation invariance of L^{n-m}.
    Supporting lemma; the proof is supplied. *)
Lemma affine_invariant_integral_translation (v : X -> R) (z : Vn) :
  KX v -> affine_invariant_integral (v \o Aact (isometry_of eO z)) = affine_invariant_integral v.
Proof.
move=> hv.
have hgl := topological_group_laws (lch_group_topological hG).
have hw : KX (v \o Aact (isometry_of eO z)) := compactly_supported_translate hgl hXA _ hv.
have hh := compactly_supported_compose hxic hxip hv.
have hh' := compactly_supported_compose hxic hxip hw.
rewrite /affine_invariant_integral.
rewrite (compact_daniell_iterations_commute hOH hOL hEkH hEkl hTD hLD hh').
rewrite (compact_daniell_iterations_commute hOH hOL hEkH hEkl hTD hLD hh).
apply: (congr1 Theta); apply: funext=> s.
transitivity (Lamk (fun y => (fun y' => v (xi (s, y'))) (y + pm p (om (invO s) z)))).
  apply: (congr1 Lamk); apply: funext=> y.
  change (v (Aact (isometry_of eO z) (xi (s, y))) = v (xi (s, y + pm p (om (invO s) z)))).
  by rewrite (affine_parametrisation_translate hmn hO).
exact: (lebesgue_integral_shift _ (affine_section_translation s hv)).
Qed.

(** Source for [affine_invariant_integral_invariant]: "a G invariant
    integral mu on K(X) is given by the formula mu(v) = int int
    v[s(p^{-1}{y})] dtheta_n s dL^{n-m} y whenever v in K(X)", Federer
    2.7.16, p. 140, in the sense of 2.7.1, p. 122; mu is moreover
    monotone. Direct formalisation: every isometry is tau_z o (tau_0 o t). *)
Theorem affine_invariant_integral_invariant :
  is_invariant_integral Aact affine_invariant_integral /\
  is_monotone_daniell_integral KX affine_invariant_integral.
Proof.
have hM := affine_invariant_integral_monotone.
split; last exact: hM.
split; first exact: monotone_daniell_is_daniell hM.
move=> v g hv; rewrite mul1r.
have hgl := topological_group_laws (lch_group_topological hG).
have he : g = mulS (isometry_of eO (isometry_translation g)) (isometry_of (isometry_linear g) 0).
  apply: (isometry_ext)=> w; rewrite (isometry_map_mul hS) !isometry_of_mapE (orthogonal_element_unit hO).
  by rewrite add0r.
have -> : v \o Aact g = (v \o Aact (isometry_of eO (isometry_translation g))) \o
    Aact (isometry_of (isometry_linear g) 0).
  apply: funext=> S; change (v (Aact g S) = v (Aact (isometry_of eO (isometry_translation g))
    (Aact (isometry_of (isometry_linear g) 0) S))).
  by rewrite -(affine_subspace_action_compatible hS) -he.
have hw : KX (v \o Aact (isometry_of eO (isometry_translation g))) := compactly_supported_translate hgl hXA _ hv.
rewrite (affine_invariant_integral_rotation (isometry_linear g) hw).
exact: (affine_invariant_integral_translation (isometry_translation g) hv).
Qed.

(** Source for [affine_space_sigma_compact]: X is a countable union of
    compact sets, the images under xi of O(n) x {y : |y| <= j},
    supporting 2.7.15, p. 133, for Federer 2.7.16, p. 141. Supporting
    lemma. *)
Lemma affine_space_sigma_compact : is_sigma_compact_space X.
Proof.
exists (fun j : nat => xi @` ([set: O] `*` [set y : Ek | `|y - 0| <= j%:R])); split.
- move=> j; apply: continuous_compact; first exact: continuous_subspaceT hxic.
  by apply: compact_setX=> //; exact: (@euclidean_closed_ball_compact R k).
- move=> S _; have [[s y] <-] := affine_parametrisation_onto hmn hO p S.
  exists (Num.truncn `|y|).+1=> //; exists (s, y)=> //; split=> //=.
  by rewrite subr0; have /andP[_ h] := truncn_itv (normr_ge0 y); exact: ltW.
Qed.

(** Source for [affine_invariant_measure_invariant]: "to verify that
    gamma is invariant under the action of G", Federer 2.7.16, p. 141:
    gamma is a G invariant measure over X in the sense of 2.7.1,
    p. 122, the K(X) regular measure associated with mu. Direct
    formalisation: the K(X) regular measure of mu is a Radon measure by
    2.7.15, p. 133, and two Radon measures representing mu coincide. *)
Theorem affine_invariant_measure_invariant : is_invariant_measure Aact affine_invariant_measure.
Proof.
have [hI hM] := affine_invariant_integral_invariant.
have hC := covariant_integral_law hI.
have [phi [hphiC hphim hphirep hphireg _]] := covariant_measure_exists hM hC.
have hphir : is_radon_measure phi.
  exact: (homogeneous_covariant_measure_radon hG hXA hXH hXl hphiC (or_intror affine_space_sigma_compact)).
have he : phi = affine_invariant_measure.
  exact: (radon_representations_coincide hphim affine_invariant_measure_is_measure hphir
    affine_invariant_measure_radon hphirep affine_invariant_measure_represents).
by exists affine_invariant_integral; split=> //; rewrite -he.
Qed.

Section Alternate.
Variable psi : set OP -> \bar R.
Hypothesis hpsi : is_normalised_invariant_measure (orthogonal_projection_action hBk hBn hbn hO) psi.
Variable Psi : (OP -> R) -> R.
Hypothesis hPsi : is_real_integral_functional psi KOP Psi.

(** Source for [affine_invariant_integral_alternate]: "the function
    mapping s onto p s^{-1} carries theta_n onto theta*_{n,n-m} [see
    (6)], we obtain the alternate formula mu(v) = int int v(q^{-1}{y})
    dtheta*_{n,n-m} q dL^{n-m} y", Federer 2.7.16, p. 141, for every
    normalised O(n) invariant measure psi = theta*_{n,n-m} over
    O*(n, n - m) and every Psi represented by psi. Direct formalisation:
    psi = (A^p)_# theta_n by example (6), and q |-> v(q^{-1}{y}) is
    continuous because its composite with the open orbit map A^p is
    s |-> v(xi(s, y)) (affine_parametrisation_fibre). *)
Theorem affine_invariant_integral_alternate (v : X -> R) :
  KX v -> affine_invariant_integral v = Lamk (fun y => Psi (fun q => v (fibre q y))).
Proof.
move=> hv.
pose Ap := orthogonal_projection_action hBk hBn hbn hO.
have hAP := orthogonal_projections_homogeneous hBk hbk hO.
have hOPc : compact [set: OP] := orthogonal_projections_compact hbk hO.
have hOPH : hausdorff_space OP := @orthogonal_projections_hausdorff R Vk Vn Bk Bn hBk hBn n _ hbn.
have [phi [hphi huniq hall]] := orthogonal_projections_invariant_measure hbk hO p.
have hpsiphi : psi = phi := huniq psi hpsi.
have hpush : measure_pushforward (orbit_map Ap p) theta = phi := hall theta p htheta.
have hApc : continuous (orbit_map Ap p) := orbit_map_continuous hAP p.
have hApp : is_proper_map (orbit_map Ap p) := compact_homogeneous_orbit_proper hOc hAP hOPH.
have hrep' := daniell_pushforward_integral hApc hApp hthm hTrep.
rewrite hpush -hpsiphi in hrep'.
rewrite /affine_invariant_integral; apply: (congr1 Lamk); apply: funext=> y.
pose F := fun q : OP => v (fibre q y).
have hFA : F \o orbit_map Ap p = (fun s => v (xi (s, y))).
  apply: funext=> s; change (v (fibre (Ap s p) y) = v (xi (s, y))).
  by rewrite (affine_parametrisation_fibre hmn hO).
have hFc : continuous (F : OP -> real_line_metric R).
  apply: (open_map_factor_continuous (homogeneous_orbit_open hAP p)).
    move=> q; have [s _ <-] : (orbit_map Ap p @` [set: O]) q by rewrite (homogeneous_orbit_onto hAP p).
    by exists s.
  rewrite hFA; exact: (affine_section_rotation y hv).1.
have hFK : KOP F := compact_space_continuous_compact hOPc hFc.
rewrite -/F (real_integral_functional_unique_on_lattice hPsi hrep' hFK).
by rewrite /daniell_pushforward hFA.
Qed.

End Alternate.

End InvariantMeasure.
