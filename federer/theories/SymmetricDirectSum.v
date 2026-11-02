(** Federer (1969), 1.9.2, p. 42: the symmetric algebra of a binary direct
    sum is the ordinary tensor product of the symmetric algebras. The
    splitting is specified by its linear maps and laws. The proof follows
    the mutually inverse graded maps in these passages. Arbitrary fields and
    arbitrary-dimensional spaces are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded SymmetricUP SymmetricAlgebra
  SymmetricGrading SymmetricMaps OrdinaryTensorMultiplication.
From Federer Require Import UnitalGradedTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_unital]: Federer 1.9.2, p. 42, the displayed
    direct- sum isomorphism. Supporting definition or claim, in words:
    Package the symmetric algebra and its grading as a unital graded
    algebra. *)
Definition symmetric_unital (K : fieldType) (V : lmodType K) : unital_graded_algebra K :=
  @UnitalGradedAlgebra K (symmetric_algebra V) (symmetric_grading V) (@symmetric_product_graded K V).

Section Alpha.
Variable K : fieldType.
Variables V P Q : lmodType K.
Variables (f : {linear V -> P}) (g : {linear V -> Q}).
Local Notation EP := (symmetric_unital P).
Local Notation EQ := (symmetric_unital Q).
Local Notation T := (unital_graded_tensor EP EQ false).

(** Source for [symmetric_tensor_commutative]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The ordinary tensor product of the two commutative symmetric
    algebras is commutative. *)
Lemma symmetric_tensor_commutative : commutative (alg_mul T).
Proof.
exact: (@ordinary_tensor_commutative K (unital_graded_view EP) (unital_graded_view EQ)
  (@symmetric_product_commute K P) (@symmetric_product_commute K Q)).
Qed.

(** Source for [symmetric_sum_generator]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: Send v to f(v) tensor 1 plus 1 tensor g(v), inserting each vector
    as a generator. *)
Definition symmetric_sum_generator v : T :=
  tensor_inj (symmetric_generator (f v)) (symmetric_unit Q) +
    tensor_inj (symmetric_unit P) (symmetric_generator (g v)).

(** Source for [symmetric_sum_generator_linear]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The prescribed map on generators is linear. *)
Lemma symmetric_sum_generator_linear : linear symmetric_sum_generator.
Proof.
move=> a v w; rewrite /symmetric_sum_generator !linearP
  !tensor_inj_addl !tensor_inj_addr !tensor_inj_scalel !tensor_inj_scaler.
by rewrite scalerDr addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V T *:%R symmetric_sum_generator symmetric_sum_generator_linear.

(** Source for [symmetric_sum_generator_homogeneous]: Federer 1.9.2, p. 42,
    the displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The prescribed generator images have degree one. *)
Lemma symmetric_sum_generator_homogeneous v : homogeneous (unital_grading T) 1 (symmetric_sum_generator v).
Proof.
apply: homogeneousD.
- exact: tensor_homogeneous_pure (symmetric_generator_homogeneous (f v)) (symmetric_unit_homogeneous Q).
- exact: tensor_homogeneous_pure (symmetric_unit_homogeneous P) (symmetric_generator_homogeneous (g v)).
Qed.

(** Source for [symmetric_sum_forward]: Federer 1.9.2, p. 42, the displayed
    direct-sum isomorphism. Supporting definition or claim, in words: Extend
    the generator map uniquely to the forward unital algebra homomorphism. *)
Definition symmetric_sum_forward : algebra_map (symmetric_algebra V) T :=
  symmetric_algebra_extension (GRing.Linear.clone _ _ _ _ symmetric_sum_generator _)
    symmetric_tensor_commutative.

(** Source for [symmetric_sum_forwardE]: Federer 1.9.2, p. 42, the displayed
    direct-sum isomorphism. Supporting definition or claim, in words: The
    forward map has the prescribed two-term value on every generator. *)
Lemma symmetric_sum_forwardE v : symmetric_sum_forward (symmetric_generator v) =
  tensor_inj (symmetric_generator (f v)) (symmetric_unit Q) +
    tensor_inj (symmetric_unit P) (symmetric_generator (g v)).
Proof. exact: symmetric_algebra_extension_generator. Qed.

(** Source for [symmetric_sum_forward_graded]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The forward map preserves homogeneous degrees. *)
Lemma symmetric_sum_forward_graded : preserves_grading (symmetric_grading V) (unital_grading T) symmetric_sum_forward.
Proof.
exact: (@symmetric_algebra_extension_graded K V T (unital_grading T)
  (@unital_product_graded K T) (GRing.Linear.clone _ _ _ _ symmetric_sum_generator _)
  symmetric_sum_generator_homogeneous symmetric_tensor_commutative).
Qed.

(** Source for [symmetric_sum_forward_unique]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The forward map is the unique algebra map with the prescribed
    generator values. *)
Lemma symmetric_sum_forward_unique (h : algebra_map (symmetric_algebra V) T) :
  (forall v, h (symmetric_generator v) = symmetric_sum_generator v) -> forall x, h x = symmetric_sum_forward x.
Proof.
exact: (@symmetric_algebra_extension_unique K V T
  (GRing.Linear.clone _ _ _ _ symmetric_sum_generator _) symmetric_tensor_commutative h).
Qed.
End Alpha.

Section Beta.
Variable K : fieldType.
Variables V P Q : lmodType K.
Variables (phi : {linear P -> V}) (psi : {linear Q -> V}).
Local Notation EP := (symmetric_unital P).
Local Notation EQ := (symmetric_unital Q).
Local Notation EV := (symmetric_unital V).
Local Notation T := (unital_graded_tensor EP EQ false).

(** Source for [symmetric_sum_backward]: Federer 1.9.2, p. 42, the displayed
    direct-sum isomorphism. Supporting definition or claim, in words:
    Compose the tensor product of the two induced inclusion maps with
    multiplication. *)
Definition symmetric_sum_backward : algebra_map T (symmetric_algebra V) :=
  algebra_comp (@ordinary_Phi K EV (@symmetric_product_commute K V))
    (@unital_tensor_map K EP EQ EV EV (symmetric_algebra_map phi) (symmetric_algebra_map psi)
      (@symmetric_algebra_map_graded K P V phi) (@symmetric_algebra_map_graded K Q V psi) false).

(** Source for [symmetric_sum_backwardE]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The backward map sends a pure tensor to the product of the two
    included symmetric elements. *)
Lemma symmetric_sum_backwardE x y : symmetric_sum_backward (tensor_inj x y) =
  symmetric_product (symmetric_algebra_map phi x) (symmetric_algebra_map psi y).
Proof.
change (@ordinary_Phi K EV (@symmetric_product_commute K V)
  (tensor_map (symmetric_algebra_map phi) (symmetric_algebra_map psi) (tensor_inj x y)) =
  symmetric_product (symmetric_algebra_map phi x) (symmetric_algebra_map psi y)).
by rewrite tensor_mapE ordinary_PhiE.
Qed.

(** Source for [symmetric_sum_backward_graded]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The backward map preserves homogeneous degrees. *)
Lemma symmetric_sum_backward_graded : preserves_grading (unital_grading T) (symmetric_grading V) symmetric_sum_backward.
Proof.
move=> n x hx; apply: (@ordinary_Phi_graded K EV (@symmetric_product_commute K V)).
exact: (@tensor_map_graded K EP EQ EV EV (unital_grading EP) (unital_grading EQ)
  (unital_grading EV) (unital_grading EV) (symmetric_algebra_map phi) (symmetric_algebra_map psi)
  (@symmetric_algebra_map_graded K P V phi) (@symmetric_algebra_map_graded K Q V psi) n x hx).
Qed.
End Beta.

Section DirectSum.
Variable K : fieldType.
Variables V P Q : lmodType K.
Variables (f : {linear V -> P}) (phi : {linear P -> V})
  (g : {linear V -> Q}) (psi : {linear Q -> V}).
Hypotheses (f_phi : cancel phi f) (g_psi : cancel psi g)
  (decomposition : forall v, phi (f v) + psi (g v) = v).
Local Notation EP := (symmetric_unital P).
Local Notation EQ := (symmetric_unital Q).
Local Notation T := (unital_graded_tensor EP EQ false).
Local Notation a := (symmetric_sum_forward f g).
Local Notation b := (symmetric_sum_backward phi psi).

(** Source for [symmetric_sum_cross_left]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: Projection onto the second summand kills the first summand
    inclusion. *)
Lemma symmetric_sum_cross_left p : g (phi p) = 0.
Proof.
have h := decomposition (phi p); rewrite f_phi in h.
have hz : psi (g (phi p)) = 0.
  apply: (addrI (phi p)); by rewrite addr0.
have hg := congr1 g hz; by rewrite g_psi linear0 in hg.
Qed.

(** Source for [symmetric_sum_cross_right]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: Projection onto the first summand kills the second summand
    inclusion. *)
Lemma symmetric_sum_cross_right q : f (psi q) = 0.
Proof.
have h := decomposition (psi q); rewrite g_psi in h.
have hz : phi (f (psi q)) = 0.
  apply: (addIr (psi q)); by rewrite add0r.
have hf := congr1 f hz; by rewrite f_phi linear0 in hf.
Qed.

(** Source for [symmetric_sum_forward_left]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The forward map sends the included first symmetric algebra to its
    left tensor inclusion. *)
Lemma symmetric_sum_forward_left x : a (symmetric_algebra_map phi x) = tensor_left EP EQ x.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K P) (@symmetric_tensor_commutative K P Q)
  (algebra_comp a (symmetric_algebra_map phi)) (tensor_left_map EP EQ false)) x.
move=> p; change (a (symmetric_algebra_map phi (symmetric_generator p)) =
  tensor_inj (symmetric_generator p) (symmetric_unit Q)).
by rewrite symmetric_algebra_mapE symmetric_sum_forwardE f_phi symmetric_sum_cross_left linear0 tensor_inj0r addr0.
Qed.

(** Source for [symmetric_sum_forward_right]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The forward map sends the included second symmetric algebra to
    its right tensor inclusion. *)
Lemma symmetric_sum_forward_right y : a (symmetric_algebra_map psi y) = tensor_right EP EQ y.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K Q) (@symmetric_tensor_commutative K P Q)
  (algebra_comp a (symmetric_algebra_map psi)) (tensor_right_map EP EQ false)) y.
move=> q; change (a (symmetric_algebra_map psi (symmetric_generator q)) =
  tensor_inj (symmetric_unit P) (symmetric_generator q)).
by rewrite symmetric_algebra_mapE symmetric_sum_forwardE g_psi symmetric_sum_cross_right linear0 tensor_inj0l add0r.
Qed.

(** Source for [symmetric_sum_forwardK]: Federer 1.9.2, p. 42, the displayed
    direct-sum isomorphism. Supporting definition or claim, in words: The
    backward map is a left inverse of the forward map, by equality on
    generators. *)
Theorem symmetric_sum_forwardK : cancel a b.
Proof.
apply: (symmetric_algebra_ext (@symmetric_algebra_exists K V) (@symmetric_product_commute K V)
  (algebra_comp b a) (algebra_id (symmetric_algebra V))).
move=> v; change (b (a (symmetric_generator v)) = symmetric_generator v).
have hp : symmetric_algebra_map phi (symmetric_unit P) = symmetric_unit V.
  exact: (algebra_map_one (symmetric_algebra_map phi)).
have hq : symmetric_algebra_map psi (symmetric_unit Q) = symmetric_unit V.
  exact: (algebra_map_one (symmetric_algebra_map psi)).
rewrite symmetric_sum_forwardE linearD.
change (b (tensor_inj (symmetric_generator (f v)) (symmetric_unit Q)) +
  b (tensor_inj (symmetric_unit P) (symmetric_generator (g v))) = symmetric_generator v).
have hl : b (tensor_inj (symmetric_generator (f v)) (symmetric_unit Q)) =
    symmetric_generator (phi (f v)).
  apply: eq_trans (@symmetric_sum_backwardE K V P Q phi psi (symmetric_generator (f v)) (symmetric_unit Q)) _.
  apply: eq_trans (congr2 (@symmetric_product K V) (@symmetric_algebra_mapE K P V phi (f v)) hq) _.
  exact: symmetric_product_unitr.
have hr : b (tensor_inj (symmetric_unit P) (symmetric_generator (g v))) =
    symmetric_generator (psi (g v)).
  apply: eq_trans (@symmetric_sum_backwardE K V P Q phi psi (symmetric_unit P) (symmetric_generator (g v))) _.
  apply: eq_trans (congr2 (@symmetric_product K V) hp (@symmetric_algebra_mapE K Q V psi (g v))) _.
  exact: symmetric_product_unitl.
apply: eq_trans (congr2 (+%R) hl hr) _.
by rewrite -linearD decomposition.
Qed.

(** Source for [symmetric_sum_backwardK]: Federer 1.9.2, p. 42, the
    displayed direct-sum isomorphism. Supporting definition or claim, in
    words: The forward map is a left inverse of the backward map, by
    equality on pure tensors. *)
Theorem symmetric_sum_backwardK : cancel b a.
Proof.
apply: (tensor_ext (tensor_exists EP EQ) (linear_comp a b) (linear_id T)) => x y.
change (a (b (tensor_inj x y)) = tensor_inj x y).
rewrite symmetric_sum_backwardE.
change (a (alg_mul (symmetric_algebra V) (symmetric_algebra_map phi x)
  (symmetric_algebra_map psi y)) = tensor_inj x y).
rewrite algebra_map_mul symmetric_sum_forward_left symmetric_sum_forward_right.
exact: (@tensor_left_right K EP EQ false x y).
Qed.
End DirectSum.
