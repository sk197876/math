(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra generic_quotient.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import CentralTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.4, final parenthesis: the universal property of the
    exterior algebra with W as coefficient ring. Coefficients act
    centrally; the generator is W-linear and has square zero. *)
Section RelativeUniversalProperty.
Variable K : fieldType.
Variable W : algebra K.
Variable M : lmodType K.
Variable rho : W -> M -> M.
Variable A : algebra K.
Variable c : algebra_map W A.
Variable j : {linear M -> A}.
(** Source for [is_relative_exterior_algebra]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Definition or construction
    used to formalise this passage. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Definition is_relative_exterior_algebra : Prop :=
  (forall w x, alg_mul A (c w) x = alg_mul A x (c w)) /\
  (forall w v, j (rho w v) = alg_mul A (c w) (j v)) /\
  (forall v, alg_mul A (j v) (j v) = 0) /\
  forall (B : algebra K) (d : algebra_map W B) (f : {linear M -> B}),
    (forall w x, alg_mul B (d w) x = alg_mul B x (d w)) ->
    (forall w v, f (rho w v) = alg_mul B (d w) (f v)) ->
    (forall v, alg_mul B (f v) (f v) = 0) ->
    exists g : algebra_map A B,
      (forall w, g (c w) = d w) /\ (forall v, g (j v) = f v) /\
      (forall h : algebra_map A B,
        (forall w, h (c w) = d w) -> (forall v, h (j v) = f v) ->
        forall x, h x = g x).
End RelativeUniversalProperty.

(** Federer 1.4.4: construct the preceding object by imposing W-linearity
    in W tensor exterior_K M. No field assumption is made on W. *)
Section RelativeConstruction.
Variable K : fieldType.
Variable W : algebra K.
Hypothesis hc : commutative (alg_mul W).
Variable M : lmodType K.
Variable rho : W -> M -> M.
Local Notation E := (exterior_algebra M).
Local Notation T := (algebra_tensor W E).
Local Notation cl := (@algebra_tensor_left K W E).
Local Notation jr := (@algebra_tensor_right K W E).
(** Source for [relative_relation]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_relation w v : T :=
  jr (exterior_generator (rho w v)) - tensor_inj w (exterior_generator v).
(** Source for [relative_ideal_rel]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Inductive relative_ideal_rel : T -> Prop :=
| relative_rel_zero : relative_ideal_rel 0
| relative_rel_add x y : relative_ideal_rel x -> relative_ideal_rel y -> relative_ideal_rel (x+y)
| relative_rel_scale a x : relative_ideal_rel x -> relative_ideal_rel (a *: x)
| relative_rel_mull x y : relative_ideal_rel y -> relative_ideal_rel (alg_mul T x y)
| relative_rel_mulr x y : relative_ideal_rel x -> relative_ideal_rel (alg_mul T x y)
| relative_rel_balance w v : relative_ideal_rel (relative_relation w v).
(** Source for [relative_subspace]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_subspace : subspace T :=
  @Subspace K T relative_ideal_rel relative_rel_zero relative_rel_add relative_rel_scale.
(** Source for [relative_ideal]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_ideal : two_sided_ideal T :=
  @TwoSidedIdeal K T relative_subspace relative_rel_mull relative_rel_mulr.
(** Source for [relative_exterior_algebra]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Definition or construction
    used to formalise this passage. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Definition relative_exterior_algebra : algebra K := quotient_algebra relative_ideal.
Local Notation R := relative_exterior_algebra.
(** Source for [relative_projection]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_projection : algebra_map T R := quotient_algebra_projection relative_ideal.
(** Source for [relative_coefficient]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_coefficient : algebra_map W R :=
  algebra_comp relative_projection (algebra_tensor_left_map W E).
(** Source for [relative_generator]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_generator : {linear M -> R} :=
  linear_comp relative_projection (linear_comp (@algebra_tensor_right_map K W E)
    (GRing.Linear.clone _ _ _ _ (@exterior_generator K M) _)).
(** Source for [relative_action]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_action w x := alg_mul R (relative_coefficient w) x.
(** Source for [relative_coefficient_central]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_coefficient_central w x : relative_action w x = alg_mul R x (relative_coefficient w).
Proof.
rewrite -[x]quotient_projection_surjective.
change (alg_mul R (relative_projection (cl w)) (relative_projection (repr x)) =
  alg_mul R (relative_projection (repr x)) (relative_projection (cl w))).
by rewrite -!algebra_map_mul (algebra_tensor_left_central hc).
Qed.
(** Source for [relative_generator_balance]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_generator_balance w v :
  relative_generator (rho w v) = relative_action w (relative_generator v).
Proof.
change (relative_projection (jr (exterior_generator (rho w v))) =
  alg_mul R (relative_projection (cl w)) (relative_projection (jr (exterior_generator v)))).
rewrite -algebra_map_mul algebra_tensor_left_right.
apply/quotient_projection_eq; exact: relative_rel_balance.
Qed.
(** Source for [relative_generator_square]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_generator_square v :
  alg_mul R (relative_generator v) (relative_generator v) = 0.
Proof.
change (alg_mul R (relative_projection (algebra_tensor_right_map W E (exterior_generator v)))
  (relative_projection (algebra_tensor_right_map W E (exterior_generator v))) = 0).
rewrite -!algebra_map_mul.
change (relative_projection (algebra_tensor_right_map W E (wedge (exterior_generator v) (exterior_generator v))) = 0).
by rewrite exterior_generator_square !linear0.
Qed.
(** Source for [relative_induction]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_induction (P : R -> Prop) :
  P 0 -> (forall x y, P x -> P y -> P (x+y)) ->
  (forall a x, P x -> P (a *: x)) ->
  (forall w s, P (relative_projection (tensor_inj w (exterior_word s)))) -> forall x, P x.
Proof.
move=> h0 hD hZ hs x; rewrite -[x]quotient_projection_surjective.
elim/tensor_induction: (repr x) => [|t u ht hu|a t ht|w t].
- by rewrite linear0.
- rewrite linearD; exact: hD ht hu.
- rewrite linearZ; exact: hZ ht.
elim/exterior_word_induction: t => [|t u ht hu|a t ht|s].
- by rewrite tensor_inj0r linear0.
- rewrite tensor_inj_addr linearD; exact: hD ht hu.
- rewrite tensor_inj_scaler linearZ; exact: hZ ht.
exact: hs.
Qed.

Section Extension.
Variable B : algebra K.
Variable d : algebra_map W B.
Variable f : {linear M -> B}.
Hypothesis hd : forall w x, alg_mul B (d w) x = alg_mul B x (d w).
Hypothesis hf : forall w v, f (rho w v) = alg_mul B (d w) (f v).
Hypothesis hs : forall v, alg_mul B (f v) (f v) = 0.
Local Notation ef := (exterior_algebra_extension hs).
(** Source for [relative_tensor_map]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_tensor_map : algebra_map T B :=
  central_tensor_map (fun w x => hd w (ef x)).
(** Source for [relative_tensorE]: Federer (1969), 1.4.4, p. 20, last three
    sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Supporting lemma for this passage; not
    separately stated in the book. The local LaTeX erratum, p. 1, entry for
    book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_tensorE w x : relative_tensor_map (tensor_inj w x) = alg_mul B (d w) (ef x).
Proof. exact: central_tensorE. Qed.
(** Source for [relative_relation_killed]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_relation_killed x : relative_ideal x -> relative_tensor_map x = 0.
Proof.
elim: x / => [|x y hx ihx hy ihy|a x hx ihx|x y hy ihy|x y hx ihx|w v].
- exact: linear0.
- by rewrite linearD /= ihx ihy add0r.
- by rewrite linearZ /= ihx scaler0.
- by rewrite algebra_map_mul ihy (bil0r (alg_bilinear B)).
- by rewrite algebra_map_mul ihx (bil0l (alg_bilinear B)).
rewrite /relative_relation linearB.
change (relative_tensor_map (jr (exterior_generator (rho w v))) -
  relative_tensor_map (tensor_inj w (exterior_generator v)) = 0).
have er : relative_tensor_map (jr (exterior_generator (rho w v))) = f (rho w v).
  exact (eq_trans (@central_tensor_right K W E B d ef
    (fun w x => hd w (ef x)) (exterior_generator (rho w v)))
    (@exterior_algebra_extension_generator K M B f hs (rho w v))).
have et : relative_tensor_map (tensor_inj w (exterior_generator v)) = alg_mul B (d w) (f v).
  exact (eq_trans (relative_tensorE w (exterior_generator v))
    (congr1 (alg_mul B (d w)) (@exterior_algebra_extension_generator K M B f hs v))).
apply (eq_trans (congr2 (fun x y : B => x-y) er et)).
by rewrite hf subrr.
Qed.
(** Source for [relative_extension]: Federer (1969), 1.4.4, p. 20, last
    three sentences of the coefficient-algebra parenthesis. In words: For
    commutative coefficients W, using W itself as the coefficient ring gives
    a W-linear exterior-to-alternating homomorphism, which is an isomorphism
    when V is finite dimensional. Definition or construction used to
    formalise this passage. The local LaTeX erratum, p. 1, entry for book p.
    20 line 11, changes the printed wording to in case. *)
Definition relative_extension : algebra_map R B := quotient_algebra_lift relative_relation_killed.
(** Source for [relative_extension_projection]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_extension_projection x : relative_extension (relative_projection x) = relative_tensor_map x.
Proof. exact: quotient_algebra_liftE. Qed.
(** Source for [relative_extension_coefficient]: Federer (1969), 1.4.4, p.
    20, last three sentences of the coefficient-algebra parenthesis. In
    words: For commutative coefficients W, using W itself as the coefficient
    ring gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_extension_coefficient w : relative_extension (relative_coefficient w) = d w.
Proof.
change (relative_extension (relative_projection (cl w)) = d w).
by rewrite relative_extension_projection /algebra_tensor_left relative_tensorE algebra_map_one alg_unitr.
Qed.
(** Source for [relative_extension_generator]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_extension_generator v : relative_extension (relative_generator v) = f v.
Proof.
change (relative_extension (relative_projection (jr (exterior_generator v))) = f v).
by rewrite relative_extension_projection /algebra_tensor_right relative_tensorE
  exterior_algebra_extension_generator algebra_map_one alg_unitl.
Qed.
(** Source for [relative_extension_unique]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Supporting lemma for this
    passage; not separately stated in the book. The local LaTeX erratum, p.
    1, entry for book p. 20 line 11, changes the printed wording to in case. *)
Lemma relative_extension_unique (g : algebra_map R B) :
  (forall w, g (relative_coefficient w) = d w) ->
  (forall v, g (relative_generator v) = f v) -> forall x, g x = relative_extension x.
Proof.
move=> gc gj; apply: relative_induction => [|x y hx hy|a x hx|w s].
- by rewrite !linear0.
- by rewrite !linearD /= hx hy.
- by rewrite !linearZ /= hx.
have ej : forall x, g (relative_projection (jr x)) = ef x.
  apply (@exterior_algebra_extension_unique K M B f hs
    (algebra_comp g (algebra_comp relative_projection (algebra_tensor_right_map W E)))).
  exact: gj.
have ep : relative_projection (tensor_inj w (exterior_word s)) =
    alg_mul R (relative_coefficient w) (relative_projection (jr (exterior_word s))).
  exact (eq_trans (congr1 relative_projection (esym (@algebra_tensor_left_right K W E w (exterior_word s))))
    (@algebra_map_mul K T R relative_projection (cl w) (jr (exterior_word s)))).
rewrite relative_extension_projection (relative_tensorE w (exterior_word s)) ep algebra_map_mul.
change (alg_mul B (g (relative_coefficient w)) (g (relative_projection (jr (exterior_word s)))) = alg_mul B (d w) (ef (exterior_word s))).
exact (congr2 (alg_mul B) (gc w) (ej (exterior_word s))).
Qed.
End Extension.

(** Source for [relative_exterior_exists]: Federer (1969), 1.4.4, p. 20,
    last three sentences of the coefficient-algebra parenthesis. In words:
    For commutative coefficients W, using W itself as the coefficient ring
    gives a W-linear exterior-to-alternating homomorphism, which is an
    isomorphism when V is finite dimensional. Formalises the indicated part
    of the passage under the hypotheses in the statement below. The local
    LaTeX erratum, p. 1, entry for book p. 20 line 11, changes the printed
    wording to in case. *)
Theorem relative_exterior_exists :
  is_relative_exterior_algebra rho relative_coefficient relative_generator.
Proof.
split; first exact: relative_coefficient_central.
split; first exact: relative_generator_balance.
split; first exact: relative_generator_square.
move=> B d f hd hf hs; exists (relative_extension hd hf hs); split.
- exact: relative_extension_coefficient.
split; first exact: relative_extension_generator.
exact: relative_extension_unique.
Qed.
End RelativeConstruction.
