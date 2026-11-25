(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Graded UnitalGradedTensor.
From Federer Require Import TensorAssociator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.3, the canonical identification at the foot of the
    associativity diagram. It preserves the total grading and the signed
    product; the change of association carries no additional sign. *)
Section HomogeneousTriples.
Variable K : fieldType.
Variables A B C : lmodType K.
Variables (GA : grading A) (GB : grading B) (GC : grading C).
Local Notation GL := (tensor_grading_product (tensor_grading_product GA GB) GC).
Local Notation GR := (tensor_grading_product GA (tensor_grading_product GB GC)).
Local Notation L := (tensor_space (tensor_space A B) C).
Local Notation R := (tensor_space A (tensor_space B C)).
Local Notation assoc := (tensor_associator A B C).
Local Notation unassoc := (tensor_unassociator A B C).

(** Source for [tensor_triple_homogeneous_induction_l]: Federer (1969),
    1.3.3, p. 15, associativity diagram and following generator calculation.
    In words: The two iterated diagonal maps agree after reassociation,
    since each sends a vector to the sum of its three placements among
    tensor units. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma tensor_triple_homogeneous_induction_l (P : L -> Prop)
    (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
    (hZ : forall a x, P x -> P (a *: x))
    (hh : forall p q r a b c, homogeneous GA p a -> homogeneous GB q b ->
      homogeneous GC r c -> P (tensor_inj (tensor_inj a b) c)) : forall x, P x.
Proof.
apply: (tensor_homogeneous_induction (GA:=tensor_grading_product GA GB) (GB:=GC)) => // p r x c hx hc.
move: x hx; apply: (tensor_component_induction (GA:=GA) (GB:=GB))
  => [|x y hx hy|a x hx|u v a b huv ha hb].
- by rewrite tensor_inj0l.
- rewrite tensor_inj_addl; exact: hD hx hy.
- rewrite tensor_inj_scalel; exact: hZ hx.
exact: hh ha hb hc.
Qed.

(** Source for [tensor_associator_degree]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma tensor_associator_degree n x : grade GR n (assoc x) = assoc (grade GL n x).
Proof.
elim/tensor_triple_homogeneous_induction_l: x => [|x y hx hy|a x hx|p q r a b c ha hb hc].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
have hl := tensor_homogeneous_pure (tensor_homogeneous_pure ha hb) hc.
have hr := tensor_homogeneous_pure ha (tensor_homogeneous_pure hb hc).
rewrite tensor_associatorE (grade_homogeneous n hr) (grade_homogeneous n hl) addnA.
by case: ifP=> _; rewrite ?linear0 ?tensor_associatorE.
Qed.
(** Source for [tensor_associator_graded]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma tensor_associator_graded : preserves_grading GL GR assoc.
Proof. by move=> n x hx; rewrite /homogeneous tensor_associator_degree hx. Qed.
(** Source for [tensor_unassociator_graded]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma tensor_unassociator_graded : preserves_grading GR GL unassoc.
Proof.
move=> n x hx; rewrite /homogeneous.
apply: (can_inj (@tensor_associatorK K A B C)).
by rewrite -tensor_associator_degree tensor_unassociatorK hx.
Qed.

(** Source for [tensor_triple_homogeneous_bilinear_ext_l]: Federer (1969),
    1.3.3, p. 15, associativity diagram and following generator calculation.
    In words: The two iterated diagonal maps agree after reassociation,
    since each sends a vector to the sum of its three placements among
    tensor units. Supporting lemma for this passage; not separately stated
    in the book. *)
Lemma tensor_triple_homogeneous_bilinear_ext_l (Z : lmodType K) (f g : L -> L -> Z)
    (hf : bilinear f) (hg : bilinear g) :
  (forall p q r u v w a b c d e h,
    homogeneous GA p a -> homogeneous GB q b -> homogeneous GC r c ->
    homogeneous GA u d -> homogeneous GB v e -> homogeneous GC w h ->
    f (tensor_inj (tensor_inj a b) c) (tensor_inj (tensor_inj d e) h) =
    g (tensor_inj (tensor_inj a b) c) (tensor_inj (tensor_inj d e) h)) ->
  forall x y, f x y = g x y.
Proof.
move=> he; apply: tensor_triple_homogeneous_induction_l =>
  [y|x x' hx hx' y|k x hx y|p q r a b c ha hb hc].
- exact: eq_trans (bil0l hf y) (esym (bil0l hg y)).
- exact: eq_trans (bilDl hf x x' y)
    (eq_trans (congr2 (+%R) (hx y) (hx' y)) (esym (bilDl hg x x' y))).
- exact: eq_trans (bilZl hf k x y)
    (eq_trans (congr1 ( *:%R k) (hx y)) (esym (bilZl hg k x y))).
apply: tensor_triple_homogeneous_induction_l =>
  [|y y' hy hy'|k y hy|u v w d e h hd he' hh].
- exact: eq_trans (bil0r hf (tensor_inj (tensor_inj a b) c))
    (esym (bil0r hg (tensor_inj (tensor_inj a b) c))).
- exact: eq_trans (bilDr hf (tensor_inj (tensor_inj a b) c) y y')
    (eq_trans (congr2 (+%R) hy hy') (esym (bilDr hg (tensor_inj (tensor_inj a b) c) y y'))).
- exact: eq_trans (bilZr hf k (tensor_inj (tensor_inj a b) c) y)
    (eq_trans (congr1 ( *:%R k) hy) (esym (bilZr hg k (tensor_inj (tensor_inj a b) c) y))).
exact: he ha hb hc hd he' hh.
Qed.
End HomogeneousTriples.

Section Products.
Variable K : fieldType.
Variables A B C : unital_graded_algebra K.
Variable s : bool.
Local Notation GA := (unital_grading A).
Local Notation GB := (unital_grading B).
Local Notation GC := (unital_grading C).
Local Notation AG := (unital_graded_view A).
Local Notation BG := (unital_graded_view B).
Local Notation CG := (unital_graded_view C).
Local Notation AB := (unital_graded_tensor A B s).
Local Notation BC := (unital_graded_tensor B C s).
Local Notation ABG := (unital_graded_view AB).
Local Notation BCG := (unital_graded_view BC).
Local Notation L := (unital_graded_tensor AB C s).
Local Notation R := (unital_graded_tensor A BC s).
Local Notation assoc := (tensor_associator A B C).

(** Source for [tensor_associator_sign]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma tensor_associator_sign q r u v :
  koszul K s r (u+v) * koszul K s q u =
  koszul K s (q+r) u * koszul K s r v.
Proof.
by rewrite koszulDr koszulDl mulrAC [koszul K s r u * koszul K s q u]mulrC.
Qed.

(** Source for [tensor_associator_mul]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma tensor_associator_mul x y : assoc (alg_mul L x y) = alg_mul R (assoc x) (assoc y).
Proof.
apply: (tensor_triple_homogeneous_bilinear_ext_l (GA:=GA) (GB:=GB) (GC:=GC)
  (bilinear_post assoc (alg_bilinear L)) (bilinear_pre assoc assoc (alg_bilinear R))) x y.
move=> p q r u v w a b c d e h ha hb hc hd he hh.
change (assoc (@graded_tensor_mul K ABG CG s (tensor_inj (tensor_inj a b) c)
  (tensor_inj (tensor_inj d e) h)) =
  @graded_tensor_mul K AG BCG s (assoc (tensor_inj (tensor_inj a b) c))
    (assoc (tensor_inj (tensor_inj d e) h))).
rewrite (@graded_tensor_mulE K ABG CG s r (u+v) (tensor_inj a b) c
  (tensor_inj d e) h hc (tensor_homogeneous_pure hd he)) linearZ.
change (koszul K s r (u+v) *: assoc
  (tensor_inj (@graded_tensor_mul K AG BG s (tensor_inj a b) (tensor_inj d e)) (alg_mul C c h)) =
  @graded_tensor_mul K AG BCG s (assoc (tensor_inj (tensor_inj a b) c))
    (assoc (tensor_inj (tensor_inj d e) h))).
rewrite (@graded_tensor_mulE K AG BG s q u a b d e hb hd)
  tensor_inj_scalel linearZ !tensor_associatorE.
rewrite (@graded_tensor_mulE K AG BCG s (q+r) u a (tensor_inj b c) d (tensor_inj e h)
  (tensor_homogeneous_pure hb hc) hd).
change (koszul K s r (u+v) *: (koszul K s q u *:
    tensor_inj (alg_mul A a d) (tensor_inj (alg_mul B b e) (alg_mul C c h))) =
  koszul K s (q+r) u *: tensor_inj (alg_mul A a d)
    (@graded_tensor_mul K BG CG s (tensor_inj b c) (tensor_inj e h))).
by rewrite (@graded_tensor_mulE K BG CG s r v b c e h hc he)
  tensor_inj_scaler !scalerA tensor_associator_sign.
Qed.

(** Source for [unital_tensor_associator]: Federer (1969), 1.3.3, p. 15,
    associativity diagram and following generator calculation. In words: The
    two iterated diagonal maps agree after reassociation, since each sends a
    vector to the sum of its three placements among tensor units. Definition
    or construction used to formalise this passage. *)
Definition unital_tensor_associator : algebra_map L R :=
  @AlgebraMap K L R assoc (tensor_associatorE (alg_one A) (alg_one B) (alg_one C))
    tensor_associator_mul.
End Products.
