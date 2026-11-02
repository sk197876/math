(** Federer (1969), 2.7.16, example (2), printed pp. 136–137: "In case U =
    V, phi is a left |det|^{-n} covariant measure over G. According to 2.7.9
    we can define a left Haar integral lambda of G by the formula lambda(u)
    = int u . |det|^{-n} dphi whenever u in K(G)" (the exponent -n as
    corrected by the erratum, p. 3, book p. 136 line 29). "We also know that
    phi is right Delta_G |det|^n covariant over G." "... therefore phi is
    right |det|^n covariant." Here V has an inner product and a finite base,
    phi is a Haar measure of the additive group of X = Hom(V, V) with the
    topology of HomSpaceTopology.v, and G is the open subset of linear
    automorphisms with the sealed group operations of LinearGroupSealed.v.
    "phi ... over G" is the restriction T |-> phi(T) of phi to subsets T of
    G (open_subspace_measure). LinearGroupUnimodular.v proves the three
    covariance identities for the integral nu(u) = int u' dphi on K(G), u'
    the extension of u by 0. This module identifies the restriction of phi
    to G with the K(G) regular measure associated with nu
    (OpenSubspaceMeasure.v; X has a countable base,
    InnerSpaceCountableBase.v), so that the restriction is a left |det|^{-n}
    covariant measure, a right Delta_G |det|^n covariant measure and a right
    |det|^n covariant measure over G in the sense of 2.7.1–2.7.2, p. 122,
    and lambda(u) is the integral of u . |det|^{-n} with respect to it.
    Likewise, for U and V with dim U = m, the restriction of a Haar measure
    of Hom(U, V) to the open set of monomorphisms is the |det|^{-m}
    covariant measure of HomMonomorphismSpace.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric LinearBasis Hom HomInner MeasureUP
  CountableOpenBaseUP RadonMeasureUP CompactSupportFunctionUP FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MonotoneDaniellIntegralUP MeasureIntegralUP SummableRealFunctionUP
  CovariantIntegralUP HaarIntegralUP TopologicalGroupUP ModularFunctionUP SubtypeCompactHausdorff
  IsotropyGroupTopology HomSpaceTopology LinearGroupTopology LinearGroupSealed OpenSubspaceExtension
  HomCompositionDeterminant HomHaarCovariance HomMonomorphisms HomMonomorphismSpace
  LinearGroupUnimodular InnerSpaceCountableBase OpenSubspaceMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LinearGroupMeasure.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation KG := (@compactly_supported_continuous_functions R GL).
Local Notation KH := (@compactly_supported_continuous_functions R H).
Local Notation det := (linear_group_det hB hb).
(** Source for [hHg]: the additive group of X = Hom(V, V) is a locally
    compact Hausdorff group, Federer 2.7.16, pp. 134–136. *)
Let hHg := hom_additive_lch_group hB hB hb hb.
(** Source for [hGo]: G is open in Hom(V, V), Federer 2.7.16, p. 134. *)
Let hGo : open (linear_group hB hb) := @linear_group_set_open R V B hB n b hb.

(** Source for [hom_endomorphism_countable_open_base]: X = Hom(V, V)
    has a countable base, as presupposed by "phi is a left |det|^{-n}
    covariant measure over G", Federer 2.7.16, p. 136, through 2.5.14,
    p. 107. Supporting lemma. *)
Lemma hom_endomorphism_countable_open_base : exists U : nat -> set H, is_countable_open_base U.
Proof.
have [U hU] := inner_space_countable_open_base (hom_inner_productP hB hB hb) (hom_rank_one_baseP hb hb).
by exists U.
Qed.

Variable phi : set H -> \bar R.
Hypothesis hphi : is_left_haar_measure (fun f g : H => f + g) phi.
Local Notation phiG := (open_subspace_measure (S := linear_group hB hb) phi).

(** Source for [linear_group_haar_measure_restricted]: "phi ... over G",
    Federer 2.7.16, p. 136: if phi is a Haar measure of the additive
    group of Hom(V, V) with Haar integral mu, the restriction of phi to
    G is the K(G) regular measure associated with the integral
    nu(u) = int u' dphi of LinearGroupUnimodular.v (2.5.3, p. 94), and
    a Radon measure; every K(G) regular measure representing nu equals
    it. Supporting theorem. *)
Theorem linear_group_haar_measure_restricted :
  exists2 mu : (H -> R) -> R, is_left_haar_integral (fun f g : H => f + g) mu &
    [/\ is_measure phiG, is_real_integral_functional phiG KG (linear_group_restricted hB hb mu),
      is_function_lattice_regular KG phiG, is_radon_measure phiG &
      forall psi, is_measure psi -> is_real_integral_functional psi KG (linear_group_restricted hB hb mu) ->
        is_function_lattice_regular KG psi -> psi = phiG].
Proof.
have [mu [hmu hm hA hr]] := hphi.
have [U hU] := hom_endomorphism_countable_open_base.
have [_ hmG hAG hrG [hradG huG]] := open_subspace_measure_associated (lch_group_hausdorff hHg)
  (lch_group_locally_compact hHg) hU hGo hm hA hr (nonzero_invariant_integral_monotone hmu).
by exists mu.
Qed.

(** Source for [linear_group_haar_measure_left_covariant]: "In case
    U = V, phi is a left |det|^{-n} covariant measure over G", Federer
    2.7.16, p. 136: the restriction of phi to G is a left |det|^{-n}
    covariant measure in the sense of 2.7.1–2.7.2, p. 122. Direct
    formalisation. *)
Theorem linear_group_haar_measure_left_covariant :
  is_left_covariant_measure mul (linear_group_character hB hb) phiG.
Proof.
have [mu [hmu hm hA hr]] := hphi.
have [U hU] := hom_endomorphism_countable_open_base.
apply: (open_subspace_covariant_measure (lch_group_hausdorff hHg) (lch_group_locally_compact hHg) hU hGo
  hm hA hr (nonzero_invariant_integral_monotone hmu)).
exact: (covariant_integral_law (linear_group_haar_left_covariant hB hb hmu)).
Qed.

(** Source for [linear_group_haar_measure_left_haar]: "According to
    2.7.9 we can define a left Haar integral lambda of G by the formula
    lambda(u) = int u . |det|^{-n} dphi whenever u in K(G)", Federer
    2.7.16, p. 136, with the exponent -n of the erratum, p. 3, book
    p. 136 line 29 (the book prints |det|^n), the integral being taken
    with respect to the restriction of phi to G. Direct formalisation;
    erratum correction. *)
Theorem linear_group_haar_measure_left_haar :
  exists lambda : (GL -> R) -> R, is_left_haar_integral mul lambda /\
    forall u, KG u -> is_measure_integral phiG (real_total_integrand (fun x => u x * `|det x| ^- n))
      (lambda u)%:E.
Proof.
have [mu hmu [_ hAG _ _ _]] := linear_group_haar_measure_restricted.
exists (fun u => linear_group_restricted hB hb mu (fun x => u x * `|det x| ^- n)); split.
  have h := linear_group_left_haar_integral hB hb hmu; exact h.
move=> u hu; apply: hAG.
have h := weighted_member (@linear_group_character_continuous R V B hB n b hb) hu; exact h.
Qed.

(** Source for [linear_group_haar_measure_right_modular]: "We also know
    that phi is right Delta_G |det|^n covariant over G", Federer 2.7.16,
    p. 136, by 2.7.9(3), p. 127, for every modular function Delta_G of G
    (2.7.8, p. 126): the restriction of phi to G is a right
    Delta_G |det|^n covariant measure. Direct formalisation. *)
Theorem linear_group_haar_measure_right_modular (Delta : GL -> R) :
  is_modular_function mul inv Delta ->
  is_right_covariant_measure mul inv (fun g => Delta g * `|det g| ^+ n) phiG.
Proof.
move=> hD.
have [mu [hmu hm hA hr]] := hphi.
have [U hU] := hom_endomorphism_countable_open_base.
apply: (open_subspace_covariant_measure (lch_group_hausdorff hHg) (lch_group_locally_compact hHg) hU hGo
  hm hA hr (nonzero_invariant_integral_monotone hmu)).
exact: (covariant_integral_law (linear_group_haar_right_modular hB hb hmu hD)).
Qed.

(** Source for [linear_group_haar_measure_right_covariant]: "therefore
    phi is right |det|^n covariant", Federer 2.7.16, p. 137: the
    restriction of phi to G is a right |det|^n covariant measure in the
    sense of 2.7.1–2.7.2, p. 122. Direct formalisation; the covariance
    factor is computed in LinearGroupUnimodular.v without the image
    measure (wedge^1)_# phi. *)
Theorem linear_group_haar_measure_right_covariant :
  is_right_covariant_measure mul inv (fun g => `|det g| ^+ n) phiG.
Proof.
have [mu [hmu hm hA hr]] := hphi.
have [U hU] := hom_endomorphism_countable_open_base.
apply: (open_subspace_covariant_measure (lch_group_hausdorff hHg) (lch_group_locally_compact hHg) hU hGo
  hm hA hr (nonzero_invariant_integral_monotone hmu)).
exact: (covariant_integral_law (linear_group_haar_right_covariant hB hb hmu)).
Qed.

End LinearGroupMeasure.

Section MonomorphismMeasure.
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
Local Notation M := (set_type (hom_monomorphisms hC hc hB)).
Local Notation KM := (@compactly_supported_continuous_functions R M).
(** Source for [hXg]: the additive group of X = Hom(U, V) is a locally
    compact Hausdorff group, Federer 2.7.16, p. 136. *)
Let hXg := hom_additive_lch_group hC hB hc hb.

(** Source for [hom_space_countable_open_base]: X = Hom(U, V) has a
    countable base, as presupposed in Federer 2.7.16, p. 136, through
    2.5.14, p. 107. Supporting lemma. *)
Lemma hom_space_countable_open_base : exists W : nat -> set X, is_countable_open_base W.
Proof.
have [W hW] := inner_space_countable_open_base (hom_inner_productP hC hB hc) (hom_rank_one_baseP hc hb).
by exists W.
Qed.

Variable phi : set X -> \bar R.
Hypothesis hphi : is_left_haar_measure (fun f g : X => f + g) phi.
Local Notation phiM := (open_subspace_measure (S := hom_monomorphisms hC hc hB) phi).

(** Source for [monomorphism_haar_measure_covariant]: "If phi is a Haar
    measure of the additive group of X, then phi is |det|^{-m} covariant
    with respect to the action of G" together with "the monomorphisms
    form an open subset of X ... Moreover G acts transitively on the set
    of monomorphisms", Federer 2.7.16, p. 136: the restriction of phi to
    the open set of monomorphisms is a |det|^{-m} covariant measure over
    this homogeneous space in the sense of 2.7.1, p. 122. Direct
    formalisation of the consequence left implicit by Federer. *)
Theorem monomorphism_haar_measure_covariant :
  is_covariant_measure (monomorphism_action hC hc hB hb) (fun g => `|linear_group_det hB hb g| ^- m) phiM.
Proof.
have [mu [hmu hm hA hr]] := hphi.
have [W hW] := hom_space_countable_open_base.
apply: (open_subspace_covariant_measure (lch_group_hausdorff hXg) (lch_group_locally_compact hXg) hW
  (hom_monomorphisms_open hC hc hB hb) hm hA hr (nonzero_invariant_integral_monotone hmu)).
exact: (covariant_integral_law (monomorphism_haar_covariant hC hc hB hb hmu)).
Qed.

(** Source for [monomorphism_covariant_measure_restriction]: the K(M)
    regular measure associated with u |-> int u' dphi on the set M of
    monomorphisms (monomorphism_covariant_measure) is the restriction of
    phi to M, Federer 2.7.16, p. 136, with 2.5.3, p. 94. Direct
    formalisation of the identification. *)
Theorem monomorphism_covariant_measure_restriction (mu : (X -> R) -> R) (psi : set M -> \bar R) :
  is_left_haar_integral (fun f g : X => f + g) mu -> is_real_integral_functional phi
    (@compactly_supported_continuous_functions R X) mu ->
  is_covariant_measure (monomorphism_action hC hc hB hb) (fun g => `|linear_group_det hB hb g| ^- m) psi ->
  is_real_integral_functional psi KM (open_restricted_integral mu) -> psi = phiM.
Proof.
move=> hmu hA [nu [_ _ hpsi _ hrpsi]] hApsi.
have [mu' [hmu' hm hA' hr]] := hphi.
have [W hW] := hom_space_countable_open_base.
have [_ _ _ _ [_ huniq]] := open_subspace_measure_associated (S := hom_monomorphisms hC hc hB)
  (lch_group_hausdorff hXg) (lch_group_locally_compact hXg) hW (hom_monomorphisms_open hC hc hB hb)
  hm hA hr (nonzero_invariant_integral_monotone hmu).
exact: huniq.
Qed.

End MonomorphismMeasure.
