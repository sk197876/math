(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import ExteriorCore.
From Federer Require Import UnitalGradedTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_unital]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Definition or construction used to formalise this passage. *)
Definition exterior_unital (K : fieldType) (V : lmodType K) : unital_graded_algebra K :=
  @UnitalGradedAlgebra K (exterior_algebra V) (exterior_grading V) (@wedge_graded K V).

(** Federer 1.3.2, first two paragraphs: alpha is the homomorphism with
    alpha(v) = f(v) tensor 1 + 1 tensor g(v). *)
Section Alpha.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variables V P Q : lmodType K.
Variables (f : {linear V -> P}) (g : {linear V -> Q}).
Local Notation EP := (exterior_unital P).
Local Notation EQ := (exterior_unital Q).
Local Notation T := (unital_graded_tensor EP EQ true).

(** Source for [exterior_tensor_anticommutative]: Federer (1969), 1.3.2, p.
    14, direct-sum isomorphism and the maps alpha and beta. In words: The
    exterior algebra of a direct sum is canonically isomorphic to the signed
    tensor product of the exterior algebras; the displayed alpha and beta
    are inverse maps. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma exterior_tensor_anticommutative :
  graded_anticommutative (unital_grading T) (alg_mul T).
Proof.
exact: (@signed_tensor_anticommutative K (unital_graded_view EP) (unital_graded_view EQ)
  (@exterior_anticommutative K P) (@exterior_anticommutative K Q)).
Qed.

(** Source for [alpha_generator]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Definition or construction used to formalise this passage. *)
Definition alpha_generator v : T :=
  tensor_inj (exterior_generator (f v)) (exterior_unit Q) +
    tensor_inj (exterior_unit P) (exterior_generator (g v)).
(** Source for [alpha_generator_linear]: Federer (1969), 1.3.2, p. 14,
    direct-sum isomorphism and the maps alpha and beta. In words: The
    exterior algebra of a direct sum is canonically isomorphic to the signed
    tensor product of the exterior algebras; the displayed alpha and beta
    are inverse maps. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alpha_generator_linear : linear alpha_generator.
Proof.
move=> a v w; rewrite /alpha_generator !linearP
  !tensor_inj_addl !tensor_inj_addr !tensor_inj_scalel !tensor_inj_scaler.
by rewrite scalerDr addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V T *:%R alpha_generator alpha_generator_linear.
(** Source for [alpha_generator_homogeneous]: Federer (1969), 1.3.2, p. 14,
    direct-sum isomorphism and the maps alpha and beta. In words: The
    exterior algebra of a direct sum is canonically isomorphic to the signed
    tensor product of the exterior algebras; the displayed alpha and beta
    are inverse maps. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alpha_generator_homogeneous v : homogeneous (unital_grading T) 1 (alpha_generator v).
Proof.
apply: homogeneousD.
- exact: tensor_homogeneous_pure (exterior_generator_homogeneous (f v)) (exterior_unit_homogeneous Q).
- exact: tensor_homogeneous_pure (exterior_unit_homogeneous P) (exterior_generator_homogeneous (g v)).
Qed.
(** Source for [alpha_generator_square]: Federer (1969), 1.3.2, p. 14,
    direct-sum isomorphism and the maps alpha and beta. In words: The
    exterior algebra of a direct sum is canonically isomorphic to the signed
    tensor product of the exterior algebras; the displayed alpha and beta
    are inverse maps. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma alpha_generator_square v : alg_mul T (alpha_generator v) (alpha_generator v) = 0.
Proof.
exact: (@degree_one_square_zero K T (unital_grading T) (alg_mul T)
  exterior_tensor_anticommutative h2 (alpha_generator v) (alpha_generator_homogeneous v)).
Qed.
(** Source for [alpha]: Federer (1969), 1.3.2, p. 14, direct-sum isomorphism
    and the maps alpha and beta. In words: The exterior algebra of a direct
    sum is canonically isomorphic to the signed tensor product of the
    exterior algebras; the displayed alpha and beta are inverse maps.
    Definition or construction used to formalise this passage. *)
Definition alpha : algebra_map (exterior_algebra V) T :=
  exterior_algebra_extension alpha_generator_square.
(** Source for [alphaE]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma alphaE v : alpha (exterior_generator v) =
  tensor_inj (exterior_generator (f v)) (exterior_unit Q) +
    tensor_inj (exterior_unit P) (exterior_generator (g v)).
Proof. exact: exterior_algebra_extension_generator. Qed.
(** Source for [alpha_graded]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma alpha_graded : preserves_grading (exterior_grading V) (unital_grading T) alpha.
Proof.
exact: (@exterior_algebra_extension_graded K V T (unital_grading T)
  (@unital_product_graded K T) (GRing.Linear.clone _ _ _ _ alpha_generator _)
  alpha_generator_homogeneous alpha_generator_square).
Qed.
(** Source for [alpha_unique]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma alpha_unique (h : algebra_map (exterior_algebra V) T) :
  (forall v, h (exterior_generator v) = alpha_generator v) -> forall x, h x = alpha x.
Proof.
exact: (@exterior_algebra_extension_unique K V T
  (GRing.Linear.clone _ _ _ _ alpha_generator _) alpha_generator_square h).
Qed.
End Alpha.

(** Federer 1.3.2, second paragraph: beta is Phi composed with the tensor
    product of wedge* phi and wedge* psi. *)
Section Beta.
Variable K : fieldType.
Variables V P Q : lmodType K.
Variables (phi : {linear P -> V}) (psi : {linear Q -> V}).
Local Notation EP := (exterior_unital P).
Local Notation EQ := (exterior_unital Q).
Local Notation EV := (exterior_unital V).
Local Notation T := (unital_graded_tensor EP EQ true).

(** Source for [beta]: Federer (1969), 1.3.2, p. 14, direct-sum isomorphism
    and the maps alpha and beta. In words: The exterior algebra of a direct
    sum is canonically isomorphic to the signed tensor product of the
    exterior algebras; the displayed alpha and beta are inverse maps.
    Definition or construction used to formalise this passage. *)
Definition beta : algebra_map T (exterior_algebra V) :=
  algebra_comp (@Phi K EV (@exterior_anticommutative K V))
    (@unital_tensor_map K EP EQ EV EV (exterior_algebra_map phi) (exterior_algebra_map psi)
      (@exterior_algebra_map_graded K P V phi) (@exterior_algebra_map_graded K Q V psi) true).
(** Source for [betaE]: Federer (1969), 1.3.2, p. 14, direct-sum isomorphism
    and the maps alpha and beta. In words: The exterior algebra of a direct
    sum is canonically isomorphic to the signed tensor product of the
    exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma betaE x y : beta (tensor_inj x y) =
  wedge (exterior_algebra_map phi x) (exterior_algebra_map psi y).
Proof.
change (@Phi K EV (@exterior_anticommutative K V)
  (tensor_map (exterior_algebra_map phi) (exterior_algebra_map psi) (tensor_inj x y)) =
  wedge (exterior_algebra_map phi x) (exterior_algebra_map psi y)).
by rewrite tensor_mapE PhiE.
Qed.
(** Source for [beta_graded]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma beta_graded : preserves_grading (unital_grading T) (exterior_grading V) beta.
Proof.
move=> n x hx; apply: (@Phi_graded K EV (@exterior_anticommutative K V)).
exact: (@tensor_map_graded K EP EQ EV EV (unital_grading EP) (unital_grading EQ)
  (unital_grading EV) (unital_grading EV) (exterior_algebra_map phi) (exterior_algebra_map psi)
  (@exterior_algebra_map_graded K P V phi) (@exterior_algebra_map_graded K Q V psi) n x hx).
Qed.
End Beta.

(** Federer 1.3.2, displayed hypotheses and inverse equations. The two
    cross-compositions are consequences of the three hypotheses, not extra
    assumptions. *)
Section DirectSum.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variables V P Q : lmodType K.
Variables (f : {linear V -> P}) (phi : {linear P -> V})
  (g : {linear V -> Q}) (psi : {linear Q -> V}).
Hypotheses (f_phi : cancel phi f) (g_psi : cancel psi g)
  (decomposition : forall v, phi (f v) + psi (g v) = v).
Local Notation EP := (exterior_unital P).
Local Notation EQ := (exterior_unital Q).
Local Notation T := (unital_graded_tensor EP EQ true).
Local Notation a := (alpha h2 f g).
Local Notation b := (beta phi psi).

(** Source for [g_phi]: Federer (1969), 1.3.2, p. 14, direct-sum isomorphism
    and the maps alpha and beta. In words: The exterior algebra of a direct
    sum is canonically isomorphic to the signed tensor product of the
    exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma g_phi p : g (phi p) = 0.
Proof.
have h := decomposition (phi p); rewrite f_phi in h.
have hz : psi (g (phi p)) = 0.
  apply: (addrI (phi p)); by rewrite addr0.
have hg := congr1 g hz; by rewrite g_psi linear0 in hg.
Qed.
(** Source for [f_psi]: Federer (1969), 1.3.2, p. 14, direct-sum isomorphism
    and the maps alpha and beta. In words: The exterior algebra of a direct
    sum is canonically isomorphic to the signed tensor product of the
    exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma f_psi q : f (psi q) = 0.
Proof.
have h := decomposition (psi q); rewrite g_psi in h.
have hz : phi (f (psi q)) = 0.
  apply: (addIr (psi q)); by rewrite add0r.
have hf := congr1 f hz; by rewrite f_phi linear0 in hf.
Qed.

(** Source for [alpha_phi]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma alpha_phi x : a (exterior_algebra_map phi x) = tensor_left EP EQ x.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K P)
  (algebra_comp a (exterior_algebra_map phi)) (tensor_left_map EP EQ true)) x.
move=> p; change (a (exterior_algebra_map phi (exterior_generator p)) =
  tensor_inj (exterior_generator p) (exterior_unit Q)).
by rewrite exterior_algebra_mapE alphaE f_phi g_phi linear0 tensor_inj0r addr0.
Qed.
(** Source for [alpha_psi]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma alpha_psi y : a (exterior_algebra_map psi y) = tensor_right EP EQ y.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K Q)
  (algebra_comp a (exterior_algebra_map psi)) (tensor_right_map EP EQ true)) y.
move=> q; change (a (exterior_algebra_map psi (exterior_generator q)) =
  tensor_inj (exterior_unit P) (exterior_generator q)).
by rewrite exterior_algebra_mapE alphaE g_psi f_psi linear0 tensor_inj0l add0r.
Qed.

(** Source for [beta_alpha]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem beta_alpha : cancel a b.
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp b a) (algebra_id (exterior_algebra V))).
move=> v; change (b (a (exterior_generator v)) = exterior_generator v).
have hp : exterior_algebra_map phi (exterior_unit P) = exterior_unit V.
  exact: (algebra_map_one (exterior_algebra_map phi)).
have hq : exterior_algebra_map psi (exterior_unit Q) = exterior_unit V.
  exact: (algebra_map_one (exterior_algebra_map psi)).
rewrite alphaE linearD.
change (b (tensor_inj (exterior_generator (f v)) (exterior_unit Q)) +
  b (tensor_inj (exterior_unit P) (exterior_generator (g v))) = exterior_generator v).
have hl : b (tensor_inj (exterior_generator (f v)) (exterior_unit Q)) =
    exterior_generator (phi (f v)).
  apply: eq_trans (@betaE K V P Q phi psi (exterior_generator (f v)) (exterior_unit Q)) _.
  apply: eq_trans (congr2 (@wedge K V) (@exterior_algebra_mapE K P V phi (f v)) hq) _.
  exact: wedge_unitr.
have hr : b (tensor_inj (exterior_unit P) (exterior_generator (g v))) =
    exterior_generator (psi (g v)).
  apply: eq_trans (@betaE K V P Q phi psi (exterior_unit P) (exterior_generator (g v))) _.
  apply: eq_trans (congr2 (@wedge K V) hp (@exterior_algebra_mapE K Q V psi (g v))) _.
  exact: wedge_unitl.
apply: eq_trans (congr2 (+%R) hl hr) _.
by rewrite -linearD decomposition.
Qed.
(** Source for [alpha_beta]: Federer (1969), 1.3.2, p. 14, direct-sum
    isomorphism and the maps alpha and beta. In words: The exterior algebra
    of a direct sum is canonically isomorphic to the signed tensor product
    of the exterior algebras; the displayed alpha and beta are inverse maps.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem alpha_beta : cancel b a.
Proof.
apply: (tensor_ext (tensor_exists EP EQ) (linear_comp a b) (linear_id T)) => x y.
change (a (b (tensor_inj x y)) = tensor_inj x y).
rewrite betaE.
change (a (alg_mul (exterior_algebra V) (exterior_algebra_map phi x)
  (exterior_algebra_map psi y)) = tensor_inj x y).
rewrite algebra_map_mul alpha_phi alpha_psi.
exact: (@tensor_left_right K EP EQ true x y).
Qed.
End DirectSum.
