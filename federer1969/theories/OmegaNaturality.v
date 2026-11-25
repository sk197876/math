(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OneFormIdentification OmegaConstruction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4: compatibility of the canonical map Omega with the dual
    maps of 1.4.1, as made explicit. It also permits the monomorphism
    argument to be checked on finite families without restricting the
    dimension of V. *)
Section Naturality.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V V' : lmodType K.
Variable W : algebra K.
Variable f : {linear V -> V'}.
(** Source for [Hom_dual]: Federer (1969), 1.4.4, pp. 19-20, canonical map
    Omega, together with the dual maps of 1.4.1. In words: The canonical map
    from exterior products of covectors to alternating forms is compatible
    with pullback Definition or construction used to formalise this passage. *)
Definition Hom_dual (a : Hom V' W) : Hom V W := hom_comp a (hom_of_linear f).
(** Source for [Hom_dualE]: Federer (1969), 1.4.4, pp. 19-20, canonical map
    Omega, together with the dual maps of 1.4.1. In words: The canonical map
    from exterior products of covectors to alternating forms is compatible
    with pullback Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma Hom_dualE a v : Hom_dual a v = a (f v).
Proof. by []. Qed.
(** Source for [Hom_dual_linear]: Federer (1969), 1.4.4, pp. 19-20,
    canonical map Omega, together with the dual maps of 1.4.1. In words: The
    canonical map from exterior products of covectors to alternating forms
    is compatible with pullback Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Hom_dual_linear : linear Hom_dual.
Proof. exact: hom_precompose_linear. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom V' W) (Hom V W)
  *:%R Hom_dual Hom_dual_linear.
(** Source for [exterior_augmentation_natural]: Federer (1969), 1.4.4, pp.
    19-20, canonical map Omega, together with the dual maps of 1.4.1. In
    words: The canonical map from exterior products of covectors to
    alternating forms is compatible with pullback Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_augmentation_natural x : exterior_augmentation V' (exterior_algebra_map f x) = exterior_augmentation V x.
Proof.
pose a := linear_comp (exterior_augmentation V') (exterior_algebra_map f).
change (a x = exterior_augmentation V x).
elim/exterior_word_induction: x => [|x y hx hy|c x hx|s].
- by rewrite !linear0.
- rewrite (linD (linearP a)) (linD (linearP (exterior_augmentation V))).
  exact (congr2 (fun x y : K => x+y) hx hy).
- rewrite (linZ (linearP a)) (linZ (linearP (exterior_augmentation V))).
  exact (congr1 (fun y : K => c*y) hx).
- change (exterior_augmentation V' (exterior_algebra_map f (exterior_word s)) =
    exterior_augmentation V (exterior_word s)).
  rewrite exterior_algebra_map_word !exterior_augmentation_word.
  by case: s.
Qed.
(** Source for [A_star_dual_coefficient]: Federer (1969), 1.4.4, pp. 19-20,
    canonical map Omega, together with the dual maps of 1.4.1. In words: The
    canonical map from exterior products of covectors to alternating forms
    is compatible with pullback Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma A_star_dual_coefficient (w : W) : A_star_dual f (coefficient_form V' w) = coefficient_form V w.
Proof.
apply: hom_finite_ext => x.
change (coefficient_form V' w (exterior_algebra_map f x) = coefficient_form V w x).
by rewrite !coefficient_formE exterior_augmentation_natural.
Qed.
(** Source for [alternating_dual_algebra_map]: Federer (1969), 1.4.4, pp.
    19-20, canonical map Omega, together with the dual maps of 1.4.1. In
    words: The canonical map from exterior products of covectors to
    alternating forms is compatible with pullback Definition or construction
    used to formalise this passage. *)
Definition alternating_dual_algebra_map :
  algebra_map (alternating_unital_algebra h2 V' W) (alternating_unital_algebra h2 V W).
Proof.
apply (@AlgebraMap K (alternating_unital_algebra h2 V' W)
  (alternating_unital_algebra h2 V W) (GRing.Linear.clone _ _ _ _ (@A_star_dual K V V' W f) _)).
- exact: A_star_dual_coefficient.
- exact: A_star_dual_multiplicative.
Defined.
(** Source for [one_generator_natural]: Federer (1969), 1.4.4, pp. 19-20,
    canonical map Omega, together with the dual maps of 1.4.1. In words: The
    canonical map from exterior products of covectors to alternating forms
    is compatible with pullback Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma one_generator_natural a : A_star_dual f (one_generator a) = one_generator (Hom_dual a).
Proof.
rewrite /one_generator A_star_dual_include.
congr (form_include _); apply: form_ext => /tupleP [v t]; rewrite (tuple0 t).
rewrite A_m_dualE.
change (one_form a [tuple f v] = one_form (Hom_dual a) [tuple v]).
by rewrite !one_formE Hom_dualE.
Qed.
Hypothesis hcomm : commutative (alg_mul W).
(** Source for [Omega_W_natural]: Federer (1969), 1.4.4, pp. 19-20,
    canonical map Omega, together with the dual maps of 1.4.1. In words: The
    canonical map from exterior products of covectors to alternating forms
    is compatible with pullback Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem Omega_W_natural x :
  A_star_dual f (Omega_W h2 V' hcomm x) =
  Omega_W h2 V hcomm (exterior_algebra_map (GRing.Linear.clone _ _ _ _ Hom_dual _) x).
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K (Hom V' W))
  (algebra_comp alternating_dual_algebra_map (Omega_W h2 V' hcomm))
  (algebra_comp (Omega_W h2 V hcomm) (exterior_algebra_map (GRing.Linear.clone _ _ _ _ Hom_dual _)))) x => a.
change (A_star_dual f (Omega_W h2 V' hcomm (exterior_generator a)) =
  Omega_W h2 V hcomm (exterior_algebra_map (GRing.Linear.clone _ _ _ _ Hom_dual _) (exterior_generator a))).
by rewrite Omega_W_generator exterior_algebra_mapE Omega_W_generator one_generator_natural.
Qed.
End Naturality.
