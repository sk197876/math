(** Federer (1969), 1.10.1, p. 44: induced dual maps on symmetric forms.
    Input spaces and the coefficient space are separate parameters,
    including in composition. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP AlgebraUP GradedAlgebra GradedComponents
  Hom HomogeneousHom BoundedHom HomogeneousSum HomFiniteFunctor
  SymmetricAlgebra SymmetricGrading SymmetricMaps SymmetricPowerFunctor
  SymmetricForms SymmetricFormWords SymmetricFormExtension
  SymmetricFormIsomorphism SymmetricPairing SymmetricFormSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Dual.
Variable K : fieldType.
Variables V V' W : lmodType K.
Variable f : {linear V -> V'}.
Local Notation hf := (@symmetric_algebra_map_graded K V V' f).
(** Source for [S_m_dual]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: A linear map induces a contravariant linear map on symmetric forms of each degree. *)
Definition S_m_dual m (phi : S_m V' W m) : S_m V W m :=
  homogeneous_sform (homogeneous_precompose hf (sform_homogeneous phi)).
(** Source for [S_star_dual]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: Precomposition gives the induced map on the full graded space. *)
Definition S_star_dual (phi : S_star V' W) : S_star V W := finite_precompose hf phi.
(** Source for [S_m_dual_linear]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The induced map in each degree is linear. *)
Lemma S_m_dual_linear m : linear (@S_m_dual m).
Proof. move=> a phi psi; by rewrite /S_m_dual !linearP. Qed.
HB.instance Definition _ m := GRing.isLinear.Build K (S_m V' W m) (S_m V W m)
  *:%R (@S_m_dual m) (@S_m_dual_linear m).
(** Source for [S_star_dual_linear]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The full induced map is linear. *)
Lemma S_star_dual_linear : linear S_star_dual.
Proof. exact: finite_precompose_linear. Qed.
HB.instance Definition _ := GRing.isLinear.Build K (S_star V' W) (S_star V W)
  *:%R S_star_dual S_star_dual_linear.
(** Source for [S_star_dualE]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The induced map evaluates by applying the symmetric algebra map to its argument. *)
Lemma S_star_dualE phi x : S_star_dual phi x = phi (symmetric_algebra_map f x).
Proof. by []. Qed.
(** Source for [S_m_dual_symmetric_pairing]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The displayed characterisation: pairing a vector with a pulled-back form equals pairing its induced symmetric image with the original form. *)
Lemma S_m_dual_symmetric_pairing m (phi : S_m V' W m) x :
  symmetric_pairing x (S_m_dual phi) = symmetric_pairing (symmetric_power_map f m x) phi.
Proof.
rewrite /symmetric_pairing /sform_to_hom /S_m_dual homogeneous_sformK
  !homogeneous_restrictE homogeneous_precomposeE.
by [].
Qed.
(** Source for [S_m_dual_unique]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: That pairing identity determines the pullback uniquely. *)
Lemma S_m_dual_unique m (phi : S_m V' W m) (psi : S_m V W m) :
  (forall x, symmetric_pairing x psi = symmetric_pairing (symmetric_power_map f m x) phi) -> psi = S_m_dual phi.
Proof. move=> h; apply: symmetric_pairing_ext => x; by rewrite S_m_dual_symmetric_pairing h. Qed.
(** Source for [S_m_dualE]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: On tuple arguments, the pullback composes every argument with the given linear map. *)
Lemma S_m_dualE m (phi : S_m V' W m) (t : m.-tuple V) :
  S_m_dual phi t = phi (map_tuple f t).
Proof.
rewrite /S_m_dual homogeneous_sformE homogeneous_precomposeE
  symmetric_algebra_map_word sform_homogeneousE sform_extensionE.
exact: (sform_wordsE phi (map_tuple f t)).
Qed.
(** Source for [S_star_dual_include]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The full pullback restricts to the degree-wise pullback. *)
Lemma S_star_dual_include m (phi : S_m V' W m) :
  S_star_dual (sform_include phi) = sform_include (S_m_dual phi).
Proof.
by rewrite /S_star_dual /sform_include /S_m_dual homogeneous_sformK finite_precompose_include.
Qed.
(** Source for [S_star_dual_component]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: Taking a homogeneous component commutes with pullback. *)
Lemma S_star_dual_component m phi :
  sform_component m (S_star_dual phi) = S_m_dual (sform_component m phi).
Proof.
by rewrite /S_star_dual /S_m_dual /sform_component homogeneous_sformK finite_precompose_piece.
Qed.
(** Source for [S_star_dual_graded]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The induced map preserves the grading. *)
Lemma S_star_dual_graded : preserves_grading (S_star_grading V' W) (S_star_grading V W) S_star_dual.
Proof.
move=> m phi hphi; change (finite_hom_grade m (S_star_dual phi) = S_star_dual phi).
rewrite -finite_precompose_grade; exact (congr1 S_star_dual hphi).
Qed.
(** Source for [S_star_dual_direct_sum]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The full induced map is the direct sum of the maps in each degree. *)
Theorem S_star_dual_direct_sum phi : exists N,
  S_star_dual phi = \sum_(i < N) sform_include (S_m_dual (sform_component i phi)).
Proof.
have [N hN] := symmetric_form_sum_decomposition phi; exists N.
rewrite {1}hN linear_sum; apply: eq_bigr => i _; exact: S_star_dual_include.
Qed.
End Dual.

(** Source for [S_dual]: Federer 1.10.1, p. 44,
    final paragraph and displayed pairing identity. In words: The scalar-valued abbreviation for the induced graded map. *)
Definition S_dual (K : fieldType) (V V' : lmodType K) (f : {linear V -> V'}) :=
  @S_star_dual K V V' K^o f.
Arguments S_dual {K V V'} f.


(** Source for [S_m_dual_id]: Federer 1.10.1, p. 44, supporting
    functoriality of the induced map. Pullback along the identity is the
    identity *)
Lemma S_m_dual_id (K : fieldType) (V W : lmodType K) m (phi : S_m V W m) :
  S_m_dual (linear_id V) phi = phi.
Proof.
apply: sform_ext=> t; rewrite S_m_dualE.
congr (phi _); apply: val_inj; by rewrite /= map_id.
Qed.

(** Source for [S_star_dual_id]: Federer 1.10.1, p. 44,
    the full induced map along the identity is the identity. This is
    the graded counterpart of the preceding degree-wise identity. *)
Lemma S_star_dual_id (K : fieldType) (V W : lmodType K) (phi : S_star V W) :
  S_star_dual (linear_id V) phi = phi.
Proof. apply: hom_finite_ext=> x; by rewrite S_star_dualE symmetric_algebra_map_id. Qed.

(** Source for [S_star_dual_comp]: Federer 1.10.1, p. 44, supporting
    contravariant composition law for the full induced map *)
Lemma S_star_dual_comp (K : fieldType) (V V' V'' W : lmodType K)
    (f : {linear V -> V'}) (g : {linear V' -> V''}) (phi : S_star V'' W) :
  S_star_dual (linear_comp g f) phi = S_star_dual f (S_star_dual g phi).
Proof.
apply: hom_finite_ext=> x.
by rewrite !S_star_dualE symmetric_algebra_map_comp.
Qed.

(** Source for [S_m_dual_comp]: Federer 1.10.1, p. 44, supporting
    contravariant composition law in each degree *)
Lemma S_m_dual_comp (K : fieldType) (V V' V'' W : lmodType K) m
    (f : {linear V -> V'}) (g : {linear V' -> V''}) (phi : S_m V'' W m) :
  S_m_dual (linear_comp g f) phi = S_m_dual f (S_m_dual g phi).
Proof.
apply: sform_ext=> t; rewrite !S_m_dualE.
congr (phi _); apply: val_inj; by rewrite /= map_comp.
Qed.
