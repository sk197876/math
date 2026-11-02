(** Federer (1969), 2.7.17, printed p. 141: "the countably many sets Ts
    corresponding to s in S ... have equal measures ... If T were
    measurable, so would the sets Ts". Federer uses without comment that an
    invariant measure in the sense of 2.7.1, p. 122, takes equal values on a
    set and on its images under the homeomorphisms A_g, and that these
    images of a measurable set are measurable. This file proves both facts
    for an arbitrary homogeneous space X of a group G and every invariant
    measure phi, that is, the K(X) regular measure associated with a
    monotone invariant integral mu. The image measure of phi under A_g,
    which assigns phi(A_g^{-1}[B]) to B, is a measure (2.1.2, p. 54)
    representing A_g#(mu) = mu on K(X) (2.5.19, p. 113, and 2.7.1, p. 122);
    it is K(X) regular because A_g is a homeomorphism with inverse
    A_{g^{-1}} and u o A_{g^{-1}} belongs to K(X) for u in K(X); the
    uniqueness of the K(X) regular measure associated with mu (2.5.2-2.5.3,
    pp. 92-95) gives phi(A_g^{-1}[B]) = phi(B) for every subset B of X. The
    transport of regularity is proved for arbitrary function lattices and
    mutually inverse maps, from the definition of the families F0, F1 and F2
    of 2.5.3, p. 94. For the right action A(g,x) = x g^{-1} of 2.7.2, p.
    122, A_g^{-1}[B] is the right translate B g. Neither. The local erratum
    has no entry for p. 141 concerning 2.7.17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP
  HomogeneousSpaceLaws FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP CompactSupportFunctionUP CompactSupportFunctionLattice
  RealIntegralFunctionalUP MeasureUP MeasurePushforward RegularDaniellRepresentation
  DaniellSpacePushforward CovariantIntegralUP CovariantIntegralLaws HaarIntegralUP
  GroupMultiplicationHomogeneous.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LatticeRegularTransport.
Variable R : realType.
Variables X Y : choiceType.
Variables (LX : set (X -> R)) (LY : set (Y -> R)).
Variables (f : X -> Y) (g : Y -> X).
Hypothesis hfg : cancel f g.
Hypothesis hgf : cancel g f.
Hypothesis hL : forall h, LX h -> LY (h \o g).

(** Source for [strict_level_inverse_transport]: the family F0 of
    Federer 2.5.3, p. 94, "the class of all sets {x : f(x) > t}
    corresponding to f in L+ and 0 < t < infinity" (paraphrase).
    Supporting lemma for 2.7.17, p. 141: g^{-1}[{h > t}] = {h o g > t},
    and h o g belongs to the second lattice. *)
Lemma strict_level_inverse_transport (S : set X) :
  function_lattice_strict_levels LX S -> function_lattice_strict_levels LY (g @^-1` S).
Proof.
case=> h [t [[hh hn] [ht ->]]]; exists (h \o g), t; split.
- by split; [exact: hL|move=> y; exact: hn].
by split.
Qed.

(** Source for [increasing_level_inverse_transport]: the family F1 of
    Federer 2.5.3, p. 94, of unions of increasing sequences in F0.
    Supporting lemma for 2.7.17, p. 141: inverse images commute with
    unions and preserve inclusions. *)
Lemma increasing_level_inverse_transport (S : set X) :
  function_lattice_increasing_levels LX S -> function_lattice_increasing_levels LY (g @^-1` S).
Proof.
case=> V [hV [hVm ->]]; exists (fun n => g @^-1` V n); split.
- by move=> n; exact: strict_level_inverse_transport.
split; first by move=> n m hnm y; exact: hVm.
by rewrite preimage_bigcup.
Qed.

(** Source for [finite_hull_inverse_transport]: the family F2 of
    Federer 2.5.3, p. 94, of intersections of decreasing sequences in
    F1 whose first member has finite measure. Supporting lemma for
    2.7.17, p. 141: the image measure of mu under f assigns to
    g^{-1}[V] the value mu(f^{-1}[g^{-1}[V]]) = mu(V). *)
Lemma finite_hull_inverse_transport (mu : set X -> \bar R) (S : set X) :
  function_lattice_finite_hulls LX mu S ->
  function_lattice_finite_hulls LY (measure_pushforward f mu) (g @^-1` S).
Proof.
case=> V [hV [hVm [hV0 ->]]]; exists (fun n => g @^-1` V n); split.
- by move=> n; exact: increasing_level_inverse_transport.
split; first by move=> n m hnm y; exact: hVm.
have hfV : f @^-1` (g @^-1` V 0%N) = V 0%N by apply/seteqP; split=> x /=; rewrite hfg.
split; first by rewrite /measure_pushforward hfV.
by rewrite preimage_bigcap.
Qed.

(** Source for [lattice_regular_inverse_pushforward]: L regularity of
    Federer 2.5.3, p. 94, "precisely the sets of finite measure admit a
    superset in F2 of equal measure" (paraphrase). Supporting lemma for
    2.7.17, p. 141: if f has the inverse g and h o g belongs to the
    second lattice for every h in the first, then the image measure of
    an LX regular measure under f is LY regular. *)
Theorem lattice_regular_inverse_pushforward (mu : set X -> \bar R) :
  is_function_lattice_regular LX mu -> is_function_lattice_regular LY (measure_pushforward f mu).
Proof.
move=> hr S; split.
- move=> hS; have [W [hSW [hW [heq hfin]]]] := (hr (f @^-1` S)).1 hS.
  exists (g @^-1` W); split; first by move=> y hy; apply: hSW; rewrite /= hgf.
  split; first exact: finite_hull_inverse_transport.
  have hfW : f @^-1` (g @^-1` W) = W by apply/seteqP; split=> x /=; rewrite hfg.
  by rewrite /measure_pushforward hfW; split.
- by case=> W [_ [_ [-> hW]]].
Qed.

End LatticeRegularTransport.

Section InvariantMeasureTranslates.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Local Notation K := (@compactly_supported_continuous_functions R X).

(** Source for [invariant_measure_preimage]: the sets Ts of Federer
    2.7.17, p. 141, "have equal measures". Supporting lemma, for an
    arbitrary homogeneous space X: an invariant measure phi in the sense
    of 2.7.1, p. 122, satisfies phi(A_g^{-1}[B]) = phi(B) for every
    subset B of X and every g in G. The image measure of phi under A_g
    represents A_g#(mu) = mu on K(X) (2.5.19, p. 113, and 2.7.1, p. 122)
    and is K(X) regular, so it equals phi by the uniqueness in 2.5.3,
    pp. 94-95. *)
Theorem invariant_measure_preimage (phi : set X -> \bar R) :
  is_invariant_measure A phi -> forall g (B : set X), phi (A g @^-1` B) = phi B.
Proof.
case=> mu [hmu hc hphi hi hr] g B.
have hL := @compactly_supported_continuous_functions_lattice R X.
have hne : exists f, K f by exists (fun _ => 0); exact: compactly_supported_zero_function.
have [phi0 [_ [_ [_ huq]]]] := monotone_daniell_regular_representation hL hmu hne.
pose psi := measure_pushforward (A g) phi.
have hpsi : is_measure psi := measure_pushforward_is_measure (A g) hphi.
have hpi : is_real_integral_functional psi K mu.
  move=> u hu.
  have h := daniell_pushforward_integral (homogeneous_translation_continuous hA g)
    (homogeneous_translation_proper hG hA g) hphi hi hu.
  by rewrite /daniell_pushforward (hc u g hu) mul1r in h.
have hpr : is_function_lattice_regular K psi.
  have hK : forall u, K u -> K (u \o A (inv g)).
    by move=> u hu; exact: (compactly_supported_translate hG hA (inv g) hu).
  exact: (lattice_regular_inverse_pushforward (homogeneous_translation_inverse_left hG hA g)
    (homogeneous_translation_inverse_right hG hA g) hK hr).
have h1 := huq psi hpsi hpi hpr B; have h2 := huq phi hphi hi hr B.
by rewrite /psi /measure_pushforward in h1; rewrite -h1 h2.
Qed.

(** Source for [invariant_measure_measurable_preimage]: "If T were
    measurable, so would the sets Ts", Federer 2.7.17, p. 141.
    Supporting lemma, for an arbitrary homogeneous space X: if B is phi
    measurable (2.1.2, p. 54), so is A_g^{-1}[B]. A test set C is
    split by A_g^{-1}[B] as A_{g^{-1}}^{-1}[C] is split by B, and the
    measures agree by invariant_measure_preimage. *)
Theorem invariant_measure_measurable_preimage (phi : set X -> \bar R) :
  is_invariant_measure A phi ->
  forall g (B : set X), measure_measurable phi B -> measure_measurable phi (A g @^-1` B).
Proof.
move=> hphi g B hB C.
have hgK := homogeneous_translation_inverse_right hG hA g.
have h := hB (A (inv g) @^-1` C).
have hI : A (inv g) @^-1` C `&` B = A (inv g) @^-1` (C `&` A g @^-1` B).
  by apply/seteqP; split=> x /=; rewrite hgK.
have hD : A (inv g) @^-1` C `\` B = A (inv g) @^-1` (C `\` A g @^-1` B).
  by apply/seteqP; split=> x /=; rewrite hgK.
by rewrite hI hD !(invariant_measure_preimage hphi) in h.
Qed.

End InvariantMeasureTranslates.

Section RightTranslates.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.

(** Source for [right_translate_preimage]: the sets Ts = {t s : t in T}
    of Federer 2.7.17, p. 141, are the inverse images of T under the
    maps A_s of the right action A(g,x) = x g^{-1} of 2.7.2, p. 122.
    Supporting lemma. *)
Lemma right_translate_preimage (T : set G) s :
  [set mul t s | t in T] = right_multiplication_action mul inv s @^-1` T.
Proof.
have hG := topological_group_laws hT.
apply/seteqP; split=> x /=.
- by case=> t ht <-; rewrite /right_multiplication_action (group_mulgK hG).
- by move=> hx; exists (mul x (inv s))=> //; rewrite (group_mulgKV hG).
Qed.

(** Source for [right_invariant_measure_translate]: "the countably many
    sets Ts ... have equal measures", Federer 2.7.17, p. 141.
    Supporting lemma: a right invariant measure (2.7.2, p. 122) takes
    the same value at T and at T s. *)
Theorem right_invariant_measure_translate (phi : set G -> \bar R) :
  is_right_invariant_measure mul inv phi -> forall (T : set G) s, phi [set mul t s | t in T] = phi T.
Proof.
move=> hphi T s; rewrite right_translate_preimage.
exact: (invariant_measure_preimage (topological_group_laws hT) (right_multiplication_homogeneous hT)
  hphi).
Qed.

(** Source for [right_invariant_measure_translate_measurable]: "If T
    were measurable, so would the sets Ts", Federer 2.7.17, p. 141.
    Supporting lemma for right invariant measures (2.7.2, p. 122). *)
Theorem right_invariant_measure_translate_measurable (phi : set G -> \bar R) :
  is_right_invariant_measure mul inv phi ->
  forall (T : set G) s, measure_measurable phi T -> measure_measurable phi [set mul t s | t in T].
Proof.
move=> hphi T s hT'; rewrite right_translate_preimage.
exact: (invariant_measure_measurable_preimage (topological_group_laws hT)
  (right_multiplication_homogeneous hT) hphi).
Qed.

End RightTranslates.
