(** Federer (1969), 1.6.3, pp. 24-25. We identify one-covectors with linear
    functionals using [one_form]. These statements hold over any field of
    characteristic different from two. The empty product is one, as in the
    existing definition of simple vectors. No finite-dimensional assumption
    is needed in this file. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors OmegaInjective SubspaceEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Covectors.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.

(** Source for [simple_covector]: Federer 1.6.3, p. 24, first sentence. In
    words: a simple m-covector is an alternating product of m one-covectors.
    Direct definition *)
Definition simple_covector m (phi : A_m V K^o m) :=
  exists alpha : 'I_m -> A_m V K^o 1,
    phi = one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) alpha.

(** Source for [Omega_product]: Federer 1.6.3, p. 24, use of the
    isomorphism from 1.4.4. Supporting identity: Omega sends a product of
    functionals to the alternating product of their one-forms. *)
Lemma Omega_product m (a : 'I_m -> Hom V K^o) :
  Omega_m h2 (e_lambda a (ord_tuple m)) =
    one_forms_wedge h2 (scalar_bilinear K) (1 : K^o)
      (fun i => one_form (a i)).
Proof.
apply: (can_inj (@form_includeK K V K^o m)).
rewrite Omega_m_include e_lambdaE /Omega Omega_W_word
  (one_forms_wedge_include h2 (scalar_bilinear K) (@mulr1 K)).
change (foldr (alternating_wedge h2 (scalar_bilinear K))
  (coefficient_form V (1 : K^o))
  [seq one_generator b | b <- [seq a i | i <- enum 'I_m]] =
  foldr (alternating_wedge h2 (scalar_bilinear K))
  (coefficient_form V (1 : K^o))
  [seq one_generator (a i) | i <- enum 'I_m]).
by rewrite -map_comp.
Qed.

(** Source for [simple_covector_Omega]: Federer 1.6.3, p. 24, transport of
    simplicity through Omega. Direct equivalence, strengthened to
    arbitrary-dimensional V using the proved injectivity of Omega. *)
Theorem simple_covector_Omega m (xi : exterior_power (Hom V K^o) m) :
  simple_covector (Omega_m h2 xi) <-> simple xi.
Proof.
split.
- move=> [alpha ha].
  have hx : xi = e_lambda (fun i => one_hom (alpha i)) (ord_tuple m).
    apply: Omega_m_injective; rewrite Omega_product.
    have he : (fun i => one_form (one_hom (alpha i))) = alpha.
      by apply: funext => i; rewrite one_homK.
    by rewrite he.
  rewrite hx; exact: product_simple.
- move=> [t ->]; rewrite tuple_product Omega_product.
  by exists (fun i => one_form (tnth t i)).
Qed.

(** Source for [simple_covector_scale]: Federer 1.6.3, p. 24, transfer
    of simple-vector properties. Supporting lemma: scalar multiples of
    a simple covector remain simple in positive degree. The restriction
    excludes the literal empty-product exception. *)
Lemma simple_covector_scale m (phi : A_m V K^o m) c :
  (0 < m)%N -> simple_covector phi -> simple_covector (c *: phi).
Proof.
move=> hm [alpha ->].
have he : (fun i => one_form (one_hom (alpha i))) = alpha.
  by apply: funext => i; rewrite one_homK.
rewrite -he -Omega_product -linearZ simple_covector_Omega.
exact: simple_scale hm (product_simple _).
Qed.

(** Source for [covector_associated]: Federer 1.6.3, p. 24, displayed
    associated subspace. In words: the one-covectors whose product with phi
    vanishes. Here one-covectors are represented by linear functionals. *)
Definition covector_associated m (phi : A_m V K^o m) (a : Hom V K^o) :=
  alternating_wedge h2 (scalar_bilinear K) (form_include phi)
    (one_generator a) = 0.

(** Source for [covector_associated_zero]: Federer 1.6.3, p. 24,
    associated subspace; supporting verification of its zero element. *)
Lemma covector_associated_zero m (phi : A_m V K^o m) :
  covector_associated phi 0.
Proof.
by rewrite /covector_associated linear0
  (bil0r (@alternating_wedge_bilinear K h2 V K^o _ (scalar_bilinear K))).
Qed.

(** Source for [covector_associated_add]: Federer 1.6.3, p. 24,
    associated subspace; supporting verification of closure under addition. *)
Lemma covector_associated_add m (phi : A_m V K^o m) a b :
  covector_associated phi a -> covector_associated phi b ->
  covector_associated phi (a+b).
Proof.
move=> ha hb; rewrite /covector_associated linearD
  (bilDr (@alternating_wedge_bilinear K h2 V K^o _ (scalar_bilinear K))).
by rewrite ha hb add0r.
Qed.

(** Source for [covector_associated_scale]: Federer 1.6.3, p. 24,
    associated subspace; supporting verification of closure under scalars. *)
Lemma covector_associated_scale m (phi : A_m V K^o m) c a :
  covector_associated phi a -> covector_associated phi (c *: a).
Proof.
move=> ha; rewrite /covector_associated linearZ
  (bilZr (@alternating_wedge_bilinear K h2 V K^o _ (scalar_bilinear K))).
by rewrite ha scaler0.
Qed.

(** Source for [covector_subspace]: Federer 1.6.3, p. 24, displayed
    associated subspace. Packages the defining predicate and its proved
    linear closure laws; the carrier consists of linear functionals. *)
Definition covector_subspace m (phi : A_m V K^o m) : subspace (Hom V K^o) :=
  @Subspace K (Hom V K^o) (covector_associated phi)
    (covector_associated_zero phi) (@covector_associated_add m phi)
    (@covector_associated_scale m phi).

(** Source for [covector_associated_Omega]: Federer 1.6.3, p. 24,
    transport through Omega. Supporting identity identifying the two
    associated-space predicates; no finite dimension is required. *)
Lemma covector_associated_Omega m (xi : exterior_power (Hom V K^o) m) a :
  covector_subspace (Omega_m h2 xi) a <-> FedererSimple.T xi a.
Proof.
change (alternating_wedge h2 (scalar_bilinear K)
  (form_include (Omega_m h2 xi)) (one_generator a) = 0 <->
  wedge (component_val xi) (exterior_generator a) = 0).
have hm := @Omega_W_wedge K h2 V (scalar_algebra K) (@mulrC K)
  (component_val xi) (exterior_generator a).
rewrite Omega_m_include -(@Omega_generator K h2 V a) -hm.
split=> h; last by rewrite h linear0.
apply: Omega_injective; by rewrite linear0.
Qed.

(** Source for [covector_subspace_Omega]: Federer 1.6.3, p. 24,
    associated-space identification through Omega. Supporting equality
    of abstract subspaces, used to transfer bases and dimensions. *)
Lemma covector_subspace_Omega m (xi : exterior_power (Hom V K^o) m) :
  covector_subspace (Omega_m h2 xi) = FedererSimple.T xi.
Proof. apply: subspace_ext => a; exact: covector_associated_Omega. Qed.

(** Source for [covector_associated_scale_nonzero]: Federer 1.6.3,
    pp. 24-25, associated-space and adapted-basis assertions. Supporting
    identity: a nonzero scalar factor does not change the associated
    space. This includes degree zero. *)
Lemma covector_associated_scale_nonzero m (phi : A_m V K^o m) c :
  c != 0 -> forall a,
    covector_subspace (c *: phi) a <-> covector_subspace phi a.
Proof.
move=> hc a; change (alternating_wedge h2 (scalar_bilinear K)
  (form_include (c *: phi)) (one_generator a) = 0 <->
  alternating_wedge h2 (scalar_bilinear K) (form_include phi) (one_generator a) = 0).
rewrite linearZ (bilZl (@alternating_wedge_bilinear K h2 V K^o _ (scalar_bilinear K))).
split=> h; last by rewrite h scaler0.
have /eqP hz := h.
by move: hz; rewrite scaler_eq0 (negbTE hc) orFb => /eqP.
Qed.
End Covectors.
