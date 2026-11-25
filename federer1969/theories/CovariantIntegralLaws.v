(** Federer (1969), 2.7.1, printed p. 122: consequences of the definition of
    chi covariant integrals. Composition with A_g maps K(X) onto K(X), since
    A_g is a homeomorphism; "In case mu <> 0, it follows that chi is a ...
    homomorphism of G into the multiplicative group R ~ {0}" (the continuity
    of chi is proved in CovariantCharacterContinuity.v); "According to
    2.5.19, chi covariance of mu is equivalent to the condition A_g#(mu) =
    chi(g) mu whenever g in G", where A_g# is daniell_pushforward of
    DaniellSpacePushforward.v and the equality holds on K(X); "From 2.5.6
    one sees that, if mu is chi covariant, then mu+ + mu- is |chi|
    covariant", proved from the formula mu+(f) + mu-(f) = sup{|mu(h)| : h in
    K(X), |h| <= f} of 2.5.6 for f in K(X)+, on which mu+ and mu- are
    defined; finally, the K(X) regular measure associated with a monotone
    chi covariant integral exists and is unique. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws FunctionLatticeUP DaniellIntegralUP
  DaniellIntegralAlgebra MonotoneDaniellIntegralUP DaniellIntegralNegation CompactSupportFunctionUP
  CompactSupportFunctionLattice ProperMapUP DaniellSpacePushforward FunctionLatticeRegularityUP
  RealIntegralFunctionalUP MeasureUP RegularDaniellRepresentation ExtendedRealBoundsUP
  DaniellVariationUP LatticeAdditiveFunctional VectorFunctionLattice VectorVariationSupremum
  CompactUniformNorm CovariantIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CovariantIntegralLaws.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [homogeneous_translation_proper]: A_g is proper, as
    required for A_g# in Federer 2.5.19, p. 113, applied in 2.7.1,
    p. 122: the inverse image of a compact set C under the
    homeomorphism A_g is the compact set A_{g^{-1}}(C). *)
Lemma homogeneous_translation_proper g : is_proper_map (A g).
Proof.
move=> C hC.
have hh := homeomorphism_with_inverse_symmetric (homogeneous_translation_homeomorphism hG hA g).
rewrite -(homeomorphism_with_inverse_image C hh).
apply: continuous_compact=> //; apply: continuous_subspaceT.
exact: homogeneous_translation_continuous hA (inv g).
Qed.

(** Source for [compactly_supported_translate]: u o A_g belongs to
    K(X) whenever u in K(X), g in G, as presupposed by "mu(u o A_g) =
    chi(g) mu(u) whenever u in K(X), g in G", Federer 2.7.1, p. 122. *)
Lemma compactly_supported_translate (u : X -> R) g : K u -> K (u \o A g).
Proof.
exact: (@compactly_supported_compose R X X (A g) (homogeneous_translation_continuous hA g)
  (homogeneous_translation_proper (g:=g)) u).
Qed.

(** Source for [compactly_supported_translate_inverse]: every member of
    K(X) is k o A_g with k = u o A_{g^{-1}} in K(X), supporting Federer
    2.7.1, p. 122. *)
Lemma compactly_supported_translate_inverse (u : X -> R) g : u = (u \o A (inv g)) \o A g.
Proof.
by apply: funext=> x; rewrite /= (homogeneous_translation_inverse_left hG hA g x).
Qed.

(** Source for [covariant_pushforward]: "According to 2.5.19, chi
    covariance of mu is equivalent to the condition A_g#(mu) =
    chi(g) mu whenever g in G", Federer 2.7.1, p. 122; the equality of
    functionals in K(X)* means equality on K(X). Direct formalisation. *)
Theorem covariant_pushforward (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_on K A chi mu <->
  forall g u, K u -> daniell_pushforward (A g) mu u = chi g * mu u.
Proof. by split=> h; [move=> g u hu; exact: h|move=> u g hu; exact: h]. Qed.

(** Source for [translation_pushforward_daniell]: A_g# maps the
    Daniell integrals on K(X) to Daniell integrals on K(X), Federer
    2.5.19, p. 113, as used in 2.7.1, p. 122. *)
Lemma translation_pushforward_daniell (mu : (X -> R) -> R) g :
  is_daniell_integral K mu -> is_daniell_integral K (daniell_pushforward (A g) mu).
Proof.
exact: (@daniell_pushforward_daniell R X X (A g) (homogeneous_translation_continuous hA g)
  (homogeneous_translation_proper (g:=g)) mu).
Qed.

(** Source for [covariant_integral_pushforward]: chi covariant
    integrals are exactly the Daniell integrals mu on K(X) with
    A_g#(mu) = chi(g) mu on K(X) whenever g in G, Federer 2.7.1,
    p. 122, by 2.5.19. *)
Theorem covariant_integral_pushforward (chi : G -> R) (mu : (X -> R) -> R) :
  is_covariant_integral A chi mu <->
  is_daniell_integral K mu /\ forall g u, K u -> daniell_pushforward (A g) mu u = chi g * mu u.
Proof.
split.
- by case=> hd hc; split=> //; apply/covariant_pushforward.
- by case=> hd hc; constructor=> //; apply/covariant_pushforward.
Qed.

(** Source for [monotone_covariant_integral]: a monotone Daniell
    integral on K(X) satisfying the chi covariance identity is a chi
    covariant integral, Federer 2.7.1, p. 122, with 2.5.6, p. 97. *)
Lemma monotone_covariant_integral (chi : G -> R) (mu : (X -> R) -> R) :
  is_monotone_daniell_integral K mu -> is_covariant_on K A chi mu -> is_covariant_integral A chi mu.
Proof. by move=> hm hc; constructor=> //; exact: monotone_daniell_is_daniell. Qed.

Section Character.
Variables (chi : G -> R) (mu : (X -> R) -> R).
Hypothesis hc : is_covariant_on K A chi mu.
Variable u : X -> R.
Hypothesis hu : K u.
Hypothesis hmu : mu u <> 0.

(** Source for [covariant_character_unit]: chi(e) = 1 when mu <> 0,
    part of "chi is a ... homomorphism of G into the multiplicative
    group R ~ {0}", Federer 2.7.1, p. 122; A_e = 1_X gives
    mu(u) = chi(e) mu(u). *)
Lemma covariant_character_unit : chi e = 1.
Proof.
have h := hc e hu; rewrite (homogeneous_unit_identity hG hA) in h.
have hu' : u \o id = u by [].
rewrite hu' -[X in X = _]mul1r in h.
by apply: (mulIf (introN eqP hmu)); rewrite -h.
Qed.

(** Source for [covariant_character_multiplicative]: chi(g h) =
    chi(g) chi(h) when mu <> 0, Federer 2.7.1, p. 122: since
    u o A_{gh} = (u o A_g) o A_h, both sides multiply mu(u) to
    mu(u o A_{gh}). *)
Lemma covariant_character_multiplicative g h : chi (mul g h) = chi g * chi h.
Proof.
have hgh : u \o A (mul g h) = (u \o A g) \o A h.
  by apply: funext=> x; rewrite /= (homogeneous_action_compatible hA).
have h1 := hc (mul g h) hu.
have h2 := hc h (compactly_supported_translate g hu).
have h3 := hc g hu.
rewrite hgh h2 h3 mulrA [chi h * chi g]mulrC in h1.
by apply: (mulIf (introN eqP hmu)); rewrite -h1.
Qed.

(** Source for [covariant_character_nonzero]: chi(g) <> 0 when
    mu <> 0, Federer 2.7.1, p. 122, "into the multiplicative group
    R ~ {0}": chi(g) chi(g^{-1}) = chi(e) = 1. *)
Lemma covariant_character_nonzero g : chi g != 0.
Proof.
apply/eqP=> h0.
have h := covariant_character_multiplicative g (inv g).
rewrite (group_mulgV hG) covariant_character_unit h0 mul0r in h.
by move/eqP: h; rewrite oner_eq0.
Qed.

(** Source for [covariant_character_inverse]: chi(g^{-1}) = chi(g)^{-1}
    when mu <> 0, supporting Federer 2.7.1, p. 122. *)
Lemma covariant_character_inverse g : chi (inv g) = (chi g)^-1.
Proof.
have h := covariant_character_multiplicative g (inv g).
rewrite (group_mulgV hG) covariant_character_unit in h.
by rewrite -[RHS]mulr1 h mulKf // covariant_character_nonzero.
Qed.

End Character.

(** Source for [covariant_variation_integral]: "From 2.5.6 one sees
    that, if mu is chi covariant, then mu+ + mu- is |chi| covariant",
    Federer 2.7.1, p. 122. Here mu+ and mu- are the variations of 2.5.5
    on K(X)+, specified by their supremum laws, and the identity holds
    on K(X)+, their domain. Following Federer, the formula
    mu+(f) + mu-(f) = sup{|mu(h)| : h in K(X), |h| <= f} of 2.5.6,
    p. 98, is used: h |-> h o A_{g^{-1}} maps
    {h : |h| <= f o A_g} onto {k : |k| <= f}, and
    |mu(k o A_g)| = |chi(g)| |mu(k)|. *)
Theorem covariant_variation_integral (chi : G -> R) (mu P Q : (X -> R) -> R) :
  is_covariant_integral A chi mu ->
  is_daniell_positive_variation K mu P -> is_daniell_negative_variation K mu Q ->
  is_covariant_on (positive_function_lattice K) A (fun g => `|chi g|) (fun f => P f + Q f).
Proof.
move=> [hd hc] hP hQ f g hf.
have hV := @compact_support_vector_lattice R X.
have hadd : is_lattice_additive_functional K mu.
  by move=> f1 f2 h1 h2; have := daniell_integral_add hd h1 h2.
have hfg : positive_function_lattice K (f \o A g).
  by split; [exact: compactly_supported_translate g hf.1|move=> x; exact: hf.2 (A g x)].
have hs0 := @finite_variation_sum_supremum_laws R X K mu hV hadd f (P f) (Q f) hf (hP f hf) (hQ f hf).
have hs1 := @finite_variation_sum_supremum_laws R X K mu hV hadd (f \o A g)
  (P (f \o A g)) (Q (f \o A g)) hfg (hP _ hfg) (hQ _ hfg).
have hz : lattice_symmetric_order_interval K (f \o A g) (fun _ => 0).
  split; first exact: compactly_supported_zero_function.
  by move=> x; rewrite normr0; exact: hf.2 (A g x).
have hmu0 : mu (fun _ => 0) = 0 by exact (daniell_integral_zero hd (compactly_supported_zero_function R X)).
have hsup : is_extended_real_supremum (symmetric_functional_absolute_values K mu (f \o A g))
    ((`|chi g| * (P f + Q f))%:E).
  constructor.
  - move=> v [h [[hh hhf] ->]].
    pose k := h \o A (inv g).
    have hk : lattice_symmetric_order_interval K f k.
      split; first exact: compactly_supported_translate (inv g) hh.
      move=> y; have := hhf (A (inv g) y).
      by rewrite /= (homogeneous_translation_inverse_right hG hA g y).
    have hhk : h = k \o A g := compactly_supported_translate_inverse h g.
    rewrite hhk (hc k g hk.1) normrM lee_fin; apply: ler_wpM2l; first exact: normr_ge0.
    have hb := extended_real_supremum_upper hs0 (ex_intro _ k (conj hk erefl)).
    by rewrite lee_fin in hb.
  - move=> d hd0.
    have h0 : (0%E <= d)%E.
      by have := hd0 _ (ex_intro _ (fun _ => 0) (conj hz erefl)); rewrite hmu0 normr0.
    case: d hd0 h0=> [b| |] hd0 h0; last by [].
    + case: (eqVneq (chi g) 0)=> hchi.
        by rewrite hchi normr0 mul0r.
      have hcpos : 0 < `|chi g| by rewrite normr_gt0.
      have hle : ((P f + Q f)%:E <= (b / `|chi g|)%:E)%E.
        apply: (extended_real_supremum_least hs0)=> v [k [[hk hkf] ->]].
        have hkg : lattice_symmetric_order_interval K (f \o A g) (k \o A g).
          by split; [exact: compactly_supported_translate g hk|move=> x; exact: hkf (A g x)].
        have := hd0 _ (ex_intro _ (k \o A g) (conj hkg erefl)).
        rewrite (hc k g hk) normrM !lee_fin=> hb.
        by rewrite ler_pdivlMr // mulrC.
      by rewrite lee_fin ler_pdivlMr // mulrC in hle; rewrite lee_fin.
    + exact: leey.
apply: EFin_inj; exact: extended_real_supremum_unique hs1 hsup.
Qed.

(** Source for [covariant_measure_exists]: "The K(X) regular measure
    associated with a monotone chi covariant (invariant) integral is
    termed a chi covariant (invariant) measure", Federer 2.7.1, p. 122:
    by 2.5.2-2.5.3 such a measure exists and is unique. *)
Theorem covariant_measure_exists (chi : G -> R) (mu : (X -> R) -> R) :
  is_monotone_daniell_integral K mu -> is_covariant_on K A chi mu ->
  exists phi : set X -> \bar R,
    [/\ is_covariant_measure A chi phi, is_measure phi, is_real_integral_functional phi K mu,
      is_function_lattice_regular K phi &
      forall nu, is_measure nu -> is_real_integral_functional nu K mu ->
        is_function_lattice_regular K nu -> forall S, phi S = nu S].
Proof.
move=> hm hc.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hne : exists f, K f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [phi [hphi [hi [hr hu]]]] := monotone_daniell_regular_representation hL hm hne.
by exists phi; split=> //; exists mu.
Qed.

End CovariantIntegralLaws.

Arguments homogeneous_translation_proper [G X mul inv e A] hG hA g _ _.
