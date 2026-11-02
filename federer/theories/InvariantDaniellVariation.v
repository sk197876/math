(** Federer (1969), 2.7.9, printed p. 127: "If sigma is left invariant, so
    are sigma+ and sigma-, hence sigma+ and sigma- are nonnegative multiples
    of a left Haar integral." This file proves the first clause, and the
    facts needed to apply 2.7.7 in the second, for an invariant integral
    sigma on K(X), X a locally compact Hausdorff homogeneous space of G
    (2.7.1, p. 121). Here sigma+ and sigma- are the variations of 2.5.5, p.
    96, specified on K(X)+ by their supremum laws. Their invariance follows,
    as Federer indicates in 2.7.1, p. 122, "From 2.5.6 one sees that, if mu
    is chi covariant, then mu+ + mu- is |chi| covariant", from
    covariant_variation_integral for chi = 1 together with sigma = sigma+ -
    sigma- on K(X)+ (2.5.5, p. 96): sigma+ = (sigma+ + sigma- + sigma)/2 and
    sigma- = (sigma+ + sigma- - sigma)/2 on K(X)+. A Haar integral is a
    functional on K(X), so sigma+ and sigma- are extended from K(X)+ to
    monotone Daniell integrals on K(X) by u |-> sigma+(u+) - sigma+(u-), as
    in 2.5.5 and 2.5.14, p. 108 (compact_positive_cone_extension). An
    additive functional on K(X) is determined by its values on K(X)+,
    because u = u+ - u- with u+, u- in K(X)+ (2.5.1, p. 91); hence the
    extensions are invariant and sigma is their difference on K(X). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP DaniellIntegralNegation
  MonotoneDaniellIntegralUP CompactSupportFunctionUP CompactSupportFunctionLattice
  VectorFunctionLattice CompactUniformNorm LatticeAdditiveFunctional PositiveDifferenceFunctional
  CompactPositiveConeExtension DaniellVariationUP DaniellVariation DaniellVariationBounds
  DaniellVariationFunctionals TopologicalGroupUP HomogeneousSpaceUP CovariantIntegralUP
  CovariantIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InvariantVariation.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Local Notation K := (@compactly_supported_continuous_functions R X).
(** Source for [hL]: K(X) is a lattice of functions, Federer 2.5.13,
    p. 106. *)
Let hL : is_function_lattice K := @compactly_supported_continuous_functions_lattice R X.
(** Source for [hV]: K(X) is a vector lattice, Federer 2.5.13,
    p. 106. *)
Let hV : is_vector_function_lattice K := @compact_support_vector_lattice R X.

(** Source for [positive_cone_agreement]: two additive functionals on
    K(X) which agree on K(X)+ agree on K(X), since u = u+ - u- with
    u+, u- in K(X)+ (Federer 2.5.1, p. 91). Supporting lemma for the
    extension of sigma+ and sigma- from K(X)+ to K(X) in 2.7.9,
    p. 127. *)
Lemma positive_cone_agreement (B1 B2 : (X -> R) -> R) :
  is_lattice_additive_functional K B1 -> is_lattice_additive_functional K B2 ->
  (forall f, positive_function_lattice K f -> B1 f = B2 f) -> forall u, K u -> B1 u = B2 u.
Proof.
move=> h1 h2 hag u hu.
have [hup hun] := positive_parts_membership hL hu.
rewrite -(positive_parts_difference u) (vector_lattice_additive_difference hV h1 hup.1 hun.1).
by rewrite (vector_lattice_additive_difference hV h2 hup.1 hun.1) !hag.
Qed.

(** Source for [positive_cone_invariance]: an additive functional on
    K(X) which is invariant on K(X)+ is invariant on K(X). Supporting
    lemma for "so are sigma+ and sigma-", Federer 2.7.9, p. 127, after
    the extension of the variations to K(X); the invariance identity is
    that of 2.7.1, p. 122, with chi = 1. *)
Lemma positive_cone_invariance (B : (X -> R) -> R) :
  is_lattice_additive_functional K B ->
  is_covariant_on (positive_function_lattice K) A (fun _ => 1) B ->
  is_covariant_on K A (fun _ => 1) B.
Proof.
move=> hB hinv u g hu; rewrite mul1r.
have hB1 : is_lattice_additive_functional K (fun v => B (v \o A g)).
  move=> v w hv hw.
  exact: hB _ _ (compactly_supported_translate hG hA g hv)
    (compactly_supported_translate hG hA g hw).
apply: (positive_cone_agreement hB1 hB _ hu)=> f hf.
by rewrite (hinv f g hf) mul1r.
Qed.

(** Source for [positive_variation_invariant_extension]: the positive
    variation tau+ of a Daniell integral tau on K(X), Federer 2.5.5,
    p. 96, if invariant on K(X)+, extends to a monotone invariant
    Daniell integral on K(X). Supporting lemma for "hence sigma+ and
    sigma- are nonnegative multiples of a left Haar integral", 2.7.9,
    p. 127; the extension is that of 2.5.14, p. 108. *)
Lemma positive_variation_invariant_extension (tau P : (X -> R) -> R) :
  hausdorff_space X -> locally_compact [set: X] -> is_daniell_integral K tau ->
  is_daniell_positive_variation K tau P ->
  is_covariant_on (positive_function_lattice K) A (fun _ => 1) P ->
  exists P' : (X -> R) -> R,
    [/\ is_monotone_daniell_integral K P', is_covariant_on K A (fun _ => 1) P' &
      forall f, positive_function_lattice K f -> P' f = P f].
Proof.
move=> hX hlX htau hP hPi.
have hPm := positive_variation_monotone_daniell hL htau hP.
have hpos f : positive_function_lattice K f -> 0 <= P f.
  by move=> hf; exact: (daniell_positive_variation_nonnegative hL htau hP hf).
have [P' [hP'm hP'e]] := compact_positive_cone_extension hX hlX
  (monotone_daniell_integral_add hPm) (monotone_daniell_integral_scale hPm) hpos.
exists P'; split=> //.
apply: positive_cone_invariance; first exact: monotone_daniell_integral_add hP'm.
move=> f g hf.
have hfg : positive_function_lattice K (f \o A g).
  by split; [exact: (compactly_supported_translate hG hA g hf.1)|move=> x; exact: hf.2 (A g x)].
by rewrite (hP'e _ hf) (hP'e _ hfg) (hPi f g hf).
Qed.

Variable sigma : (X -> R) -> R.
Hypothesis hs : is_invariant_integral A sigma.
(** Source for [hsd]: sigma is a Daniell integral on K(X), part of
    "invariant integral", Federer 2.7.1, p. 122. *)
Let hsd := covariant_integral_daniell hs.

(** Source for [invariant_integral_variations_invariant]: "If sigma
    is left invariant, so are sigma+ and sigma-", Federer 2.7.9,
    p. 127, for an invariant integral sigma on K(X) and its variations
    on K(X)+ (2.5.5, p. 96). Direct formalisation; the proof combines
    "mu+ + mu- is |chi| covariant", 2.7.1, p. 122
    (covariant_variation_integral), for chi = 1 with sigma = sigma+ -
    sigma- on K(X)+ (daniell_positive_negative_identity). *)
Theorem invariant_integral_variations_invariant (P Q : (X -> R) -> R) :
  is_daniell_positive_variation K sigma P -> is_daniell_negative_variation K sigma Q ->
  is_covariant_on (positive_function_lattice K) A (fun _ => 1) P /\
  is_covariant_on (positive_function_lattice K) A (fun _ => 1) Q.
Proof.
move=> hP hQ.
have hsum := covariant_variation_integral hG hA hs hP hQ.
have hdiff := daniell_positive_negative_identity hL hsd hP hQ.
have key f g : positive_function_lattice K f -> P (f \o A g) = P f /\ Q (f \o A g) = Q f.
  move=> hf.
  have hfg : positive_function_lattice K (f \o A g).
    by split; [exact: (compactly_supported_translate hG hA g hf.1)|move=> x; exact: hf.2 (A g x)].
  have h1 := hsum f g hf; rewrite /= normr1 mul1r in h1.
  have h2 : P (f \o A g) - Q (f \o A g) = P f - Q f.
    by rewrite -(hdiff _ hfg) -(hdiff _ hf) (covariant_integral_law hs g hf.1) mul1r.
  by split; lra.
by split=> f g hf; rewrite mul1r; [exact: (key f g hf).1|exact: (key f g hf).2].
Qed.

(** Source for [invariant_integral_variation_extensions]: Federer
    2.7.9, p. 127, "If sigma is left invariant, so are sigma+ and
    sigma-", with sigma+ and sigma- extended from K(X)+ to monotone
    Daniell integrals P, Q on K(X): P and Q are invariant, agree with
    sigma+ and sigma- on K(X)+, and sigma = P - Q on K(X). Supporting
    theorem; 2.5.5, p. 96, gives sigma = sigma+ - sigma- on K(X)+. *)
Theorem invariant_integral_variation_extensions (P0 Q0 : (X -> R) -> R) :
  hausdorff_space X -> locally_compact [set: X] ->
  is_daniell_positive_variation K sigma P0 -> is_daniell_negative_variation K sigma Q0 ->
  exists P Q : (X -> R) -> R,
    [/\ is_monotone_daniell_integral K P /\ is_covariant_on K A (fun _ => 1) P,
      is_monotone_daniell_integral K Q /\ is_covariant_on K A (fun _ => 1) Q,
      forall f, positive_function_lattice K f -> P f = P0 f /\ Q f = Q0 f &
      forall u, K u -> sigma u = P u - Q u].
Proof.
move=> hX hlX hP0 hQ0.
have [hP0i hQ0i] := invariant_integral_variations_invariant hP0 hQ0.
have [P [hPm hPi hPe]] := positive_variation_invariant_extension hX hlX hsd hP0 hP0i.
have [Q [hQm hQi hQe]] := positive_variation_invariant_extension hX hlX
  (daniell_integral_negate hL hsd) hQ0 hQ0i.
exists P, Q; split=> //.
  by move=> f hf; rewrite hPe // hQe.
apply: (positive_cone_agreement (B1 := sigma) (B2 := fun u => P u - Q u)).
- by move=> f g hf hg; exact: (daniell_integral_add hsd hf hg).
- move=> f g hf hg /=.
  rewrite (monotone_daniell_integral_add hPm hf hg) (monotone_daniell_integral_add hQm hf hg).
  by rewrite opprD addrACA.
- by move=> f hf; rewrite hPe // hQe // (daniell_positive_negative_identity hL hsd hP0 hQ0 hf).
Qed.

(** Source for [invariant_integral_variation_decomposition]: the
    conclusion of the preceding theorem for the variations sigma+ and
    sigma- of Federer 2.5.5, p. 96 (daniell_positive_variation and
    daniell_negative_variation), as used in 2.7.9, p. 127: an invariant
    integral on K(X) is the difference of two monotone invariant
    Daniell integrals on K(X). *)
Corollary invariant_integral_variation_decomposition :
  hausdorff_space X -> locally_compact [set: X] ->
  exists P Q : (X -> R) -> R,
    [/\ is_monotone_daniell_integral K P, is_covariant_on K A (fun _ => 1) P,
      is_monotone_daniell_integral K Q, is_covariant_on K A (fun _ => 1) Q &
      forall u, K u -> sigma u = P u - Q u].
Proof.
move=> hX hlX.
have [P [Q [[hPm hPi] [hQm hQi] _ hd]]] := invariant_integral_variation_extensions hX hlX
  (daniell_positive_variation_specification hL hsd)
  (daniell_negative_variation_specification hL hsd).
by exists P, Q; split.
Qed.

End InvariantVariation.
