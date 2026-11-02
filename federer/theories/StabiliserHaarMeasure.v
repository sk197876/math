(** Federer (1969), 2.7.16, example (3), printed pp. 137–138: "If phi, psi
    are Haar measures of the additive groups of Hom(W, W), Hom(Z, V), then
    xi(G) is an open set whose complement has phi x psi measure 0. ...
    Therefore every Haar measure gamma of X is right Delta_G chi^{-1}
    covariant over G." Here V has an inner product and a finite base, W is a
    subspace with an m-element base, G is the group of the linear
    automorphisms of V mapping W onto W, with any restricted group structure
    (mulS, invS, eS) of the sealed operations of the linear group, and X is
    the space of the maps f with f[W] subset W (StabiliserHomSpace.v), with
    the topology of StabiliserHaarCovariance.v. The set xi(G) is the open
    set of univalent members of X, homeomorphic to G
    (preserving_unit_homeomorphism). "gamma ... over G" is the measure T |->
    gamma(iota[T]) over G, iota the inclusion of G into X
    (stabiliser_haar_restriction). StabiliserModularFunction.v proves the
    covariance identities for the integral nu(u) = int u' dgamma on K(G), u'
    the extension by 0 of u to X through xi. This module proves that the
    measure gamma over G is the K(G) regular measure associated with nu: it
    is the image, under the homeomorphism of xi(G) onto G, of the
    restriction of gamma to the open set xi(G), which is the K(xi(G))
    regular measure associated with u |-> int u' dgamma
    (OpenSubspaceMeasure.v), and image measures under homeomorphisms
    preserve representation (2.5.19, p. 113) and K regularity
    (RegularPushforwardBijection.v). Hence gamma is a left chi covariant
    measure over G (Federer leaves this implicit in "Therefore"), a right
    Delta_G chi^{-1} covariant measure over G, and a right |det|^n
    |det(.|W)|^{m-n} covariant measure over G, in the sense of 2.7.1–2.7.2,
    p. 122. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric LinearBasis Hom HomInner ModuleQuotient
  GrassmannSubspaces InnerProductRestriction MeasureUP MeasurePushforward CountableOpenBaseUP
  CompactSupportFunctionUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MonotoneDaniellIntegralUP CovariantIntegralUP HaarIntegralUP TopologicalGroupUP ModularFunctionUP
  HomeomorphismUP DaniellSpacePushforward EquivariantPushforward RegularPushforwardBijection
  FunctionLatticeRegularUniqueness CompactSupportFunctionLattice SubtypeCompactHausdorff
  IsotropyGroupTopology HomSpaceTopology LinearGroupTopology LinearGroupSealed OpenSubspaceExtension
  SubspaceStabiliser StabiliserHomSpace StabiliserHaarCovariance StabiliserModularFunction
  InnerSpaceCountableBase OpenSubspaceMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section StabiliserMeasure.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation hH := (hom_inner_productP hB hB hb).
Variable W : subspace V.
Variable m : nat.
Hypothesis hW : grassmann_pred m W.
Local Notation Xs := (subspace_preserving_maps W).
Local Notation hX := (@restricted_inner_productP R (Hom V V) _ hH Xs).
Local Notation X := (inner_metric_space hX).
Local Notation S := (set_type (subspace_stabiliser hB hb W)).
Local Notation O := (@preserving_units R V B hB n b hb W).
Local Notation U := (set_type O).
Local Notation KX := (@compactly_supported_continuous_functions R X).
Local Notation KS := (@compactly_supported_continuous_functions R S).
Local Notation KU := (@compactly_supported_continuous_functions R U).
Local Notation chi := (stabiliser_character hW).
(** Source for [hXg]: the additive group of X is a locally compact
    Hausdorff group, Federer 2.7.16, p. 137. *)
Let hXg := preserving_additive_lch_group hB hb hW.
(** Source for [hp]: G is homeomorphic to the open set xi(G) of X,
    Federer 2.7.16, p. 137. *)
Let hp := preserving_unit_homeomorphism hB hb hW.
(** Source for [hq]: the inverse homeomorphism of G onto xi(G), Federer
    2.7.16, p. 137. *)
Let hq := homeomorphism_with_inverse_symmetric hp.

(** Source for [stabiliser_inclusion]: the inclusion iota of G into X,
    g |-> g, through which G is identified with the open set xi(G),
    Federer 2.7.16, p. 137. Definition. *)
Definition stabiliser_inclusion (g : S) : X := set_val (stabiliser_unit_map g).

(** Source for [stabiliser_haar_restriction]: "gamma ... over G",
    Federer 2.7.16, p. 137: T |-> gamma(iota[T]) for subsets T of G.
    Definition. *)
Definition stabiliser_haar_restriction (gamma : set X -> \bar R) (T : set S) : \bar R :=
  gamma (stabiliser_inclusion @` T).

(** Source for [preserving_countable_open_base]: X has a countable base,
    as presupposed in Federer 2.7.16, p. 137, through 2.5.14, p. 107.
    Supporting lemma. *)
Lemma preserving_countable_open_base : exists Y : nat -> set X, is_countable_open_base Y.
Proof.
have [N [c hc]] := preserving_basis_exists hb hW.
have [Y hY] := inner_space_countable_open_base hX hc.
by exists Y.
Qed.

(** Source for [stabiliser_haar_restriction_pushforward]: gamma over G
    is the image of the restriction of gamma to the open set xi(G) under
    the homeomorphism of xi(G) onto G, Federer 2.7.16, p. 137, with
    2.1.2, p. 54. Supporting lemma. *)
Lemma stabiliser_haar_restriction_pushforward (gamma : set X -> \bar R) :
  stabiliser_haar_restriction gamma =
    measure_pushforward (preserving_unit_map hW) (open_subspace_measure (S := O) gamma).
Proof.
apply: funext=> T; rewrite /stabiliser_haar_restriction /measure_pushforward /open_subspace_measure.
congr gamma; apply/seteqP; split.
- move=> _ [g hg <-]; exists (stabiliser_unit_map g)=> //=.
  by rewrite (homeomorphism_right_inverse hp).
- move=> _ [f hf <-]; exists (preserving_unit_map hW f)=> //.
  by rewrite /stabiliser_inclusion (homeomorphism_left_inverse hp).
Qed.

Variable gamma : set X -> \bar R.
Hypothesis hgamma : is_left_haar_measure (fun f g : X => f + g) gamma.
Local Notation gammaG := (stabiliser_haar_restriction gamma).

(** Source for [stabiliser_haar_measure_restricted]: "gamma ... over
    G", Federer 2.7.16, p. 137: if gamma is a Haar measure of the
    additive group of X with Haar integral mu, then gamma over G is the
    K(G) regular measure associated with the integral
    nu(u) = int u' dgamma of StabiliserModularFunction.v (2.5.3, p. 94);
    every K(G) regular measure representing nu equals it. Supporting
    theorem. *)
Theorem stabiliser_haar_measure_restricted :
  exists2 mu : (X -> R) -> R, is_left_haar_integral (fun f g : X => f + g) mu &
    [/\ is_measure gammaG, is_real_integral_functional gammaG KS (stabiliser_restricted hW mu),
      is_function_lattice_regular KS gammaG &
      forall psi, is_measure psi -> is_real_integral_functional psi KS (stabiliser_restricted hW mu) ->
        is_function_lattice_regular KS psi -> psi = gammaG].
Proof.
have [mu [hmu hm hA hr]] := hgamma.
have [Y hY] := preserving_countable_open_base.
have hO : open O := @preserving_units_open R V B hB n b hb W.
have [_ hmU hAU hrU _] := open_subspace_measure_associated (S := O) (lch_group_hausdorff hXg)
  (lch_group_locally_compact hXg) hY hO hm hA hr
  (nonzero_invariant_integral_monotone hmu).
have hmG : is_measure gammaG.
  rewrite stabiliser_haar_restriction_pushforward; exact: measure_pushforward_is_measure.
have hAG : is_real_integral_functional gammaG KS (stabiliser_restricted hW mu).
  rewrite stabiliser_haar_restriction_pushforward.
  exact: (daniell_pushforward_integral (homeomorphism_continuous hp)
    (homeomorphism_with_inverse_proper hp) hmU hAU).
have hrG : is_function_lattice_regular KS gammaG.
  rewrite stabiliser_haar_restriction_pushforward.
  apply: (bijection_pushforward_regular (homeomorphism_left_inverse hp)
    (homeomorphism_right_inverse hp) _ hrU)=> f hf.
  exact: (compactly_supported_compose (homeomorphism_continuous hq)
    (homeomorphism_with_inverse_proper hq) hf).
exists mu=> //; split=> // psi hpsi hApsi hrpsi; apply: funext=> T.
exact: (function_lattice_regular_representation_unique
  (@compactly_supported_continuous_functions_lattice R S) hpsi hmG hApsi hAG hrpsi hrG T).
Qed.

Section Restriction.
Variables (mulS : S -> S -> S) (invS : S -> S) (eS : S).
Hypothesis hS : is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb)
  (linear_group_unit hB hb) (subspace_stabiliser hB hb W) mulS invS eS.

(** Source for [stabiliser_haar_measure_left_covariant]: "gamma is ...
    left chi covariant over G", implicit in "Therefore every Haar measure
    gamma of X is right Delta_G chi^{-1} covariant over G", Federer
    2.7.16, p. 137, with chi(g) = |det(g|W)|^{-m} |det g|^{m-n}: gamma
    over G is a left chi covariant measure in the sense of 2.7.1–2.7.2,
    p. 122. Direct formalisation. *)
Theorem stabiliser_haar_measure_left_covariant : is_left_covariant_measure mulS chi gammaG.
Proof.
have [mu hmu [hmG hAG hrG _]] := stabiliser_haar_measure_restricted.
exists (stabiliser_restricted hW mu); split=> //.
- have h := stabiliser_restricted_monotone hW hmu; exact h.
- exact: (covariant_integral_law (stabiliser_haar_left_covariant hW hmu hS)).
Qed.

(** Source for [stabiliser_haar_measure_right_modular]: "Therefore every
    Haar measure gamma of X is right Delta_G chi^{-1} covariant over G",
    Federer 2.7.16, p. 137, for every modular function Delta_G of G
    (2.7.8, p. 126): gamma over G is a right Delta_G chi^{-1} covariant
    measure. Direct formalisation. *)
Theorem stabiliser_haar_measure_right_modular (Delta : S -> R) :
  is_modular_function mulS invS Delta ->
  is_right_covariant_measure mulS invS (fun g => Delta g * (chi g)^-1) gammaG.
Proof.
move=> hD.
have [mu hmu [hmG hAG hrG _]] := stabiliser_haar_measure_restricted.
exists (stabiliser_restricted hW mu); split=> //.
- have h := stabiliser_restricted_monotone hW hmu; exact h.
- exact: (covariant_integral_law (stabiliser_haar_right_modular hW hmu hS hD)).
Qed.

(** Source for [stabiliser_haar_measure_right_covariant]: the right
    covariance which "the commutative diagram in (2)" yields in Federer
    2.7.16, p. 138: gamma over G is a right |det|^n |det(.|W)|^{m-n}
    covariant measure, the factor at g being |det(f |-> f o g^{-1})|^{-1}.
    Direct formalisation; the determinant of right composition is
    computed in StabiliserHaarCovariance.v instead of transporting gamma
    by wedge^1. *)
Theorem stabiliser_haar_measure_right_covariant :
  is_right_covariant_measure mulS invS
    (fun g => `|stabiliser_det g| ^+ n * `|stabiliser_restriction_det hW g| ^- (n - m)) gammaG.
Proof.
have [mu hmu [hmG hAG hrG _]] := stabiliser_haar_measure_restricted.
exists (stabiliser_restricted hW mu); split=> //.
- have h := stabiliser_restricted_monotone hW hmu; exact h.
- exact: (covariant_integral_law (stabiliser_haar_right_covariant hW hmu hS)).
Qed.

End Restriction.

End StabiliserMeasure.
