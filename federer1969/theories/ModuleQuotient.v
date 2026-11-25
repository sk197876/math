(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg generic_quotient.
From mathcomp.classical Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

(** Quotients by arbitrary subspaces. Subspace membership is a proposition;
    MathComp's classical [asbool] supplies the boolean equivalence relation
    required by [generic_quotient]. *)
Section Subspace.
Variable K : fieldType.
Variable M : lmodType K.

(** Source for [subspace]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Record subspace : Type := Subspace {
  subspace_mem :> M -> Prop;
  subspace_zero : subspace_mem 0;
  subspace_add : forall x y, subspace_mem x -> subspace_mem y -> subspace_mem (x + y);
  subspace_scale : forall a x, subspace_mem x -> subspace_mem (a *: x)
}.

(** Source for [subspace_opp]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma subspace_opp (S : subspace) x : S x -> S (- x).
Proof. by move=> hx; rewrite -scaleN1r; exact: subspace_scale hx. Qed.
(** Source for [subspace_sub]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma subspace_sub (S : subspace) x y : S x -> S y -> S (x - y).
Proof. by move=> hx hy; exact: (subspace_add hx (subspace_opp hy)). Qed.
End Subspace.

Section Quotient.
Variable K : fieldType.
Variable M : lmodType K.
Variable S : subspace M.

(** Source for [quotient_rel]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition quotient_rel (x y : M) := `[< S (x - y) >].

(** Source for [quotient_rel_refl]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_rel_refl : reflexive quotient_rel.
Proof. by move=> x; apply/asboolP; rewrite subrr; exact: subspace_zero. Qed.
(** Source for [quotient_rel_sym]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_rel_sym : symmetric quotient_rel.
Proof.
move=> x y; apply/idP/idP => /asboolP h; apply/asboolP;
  by rewrite -opprB; exact: subspace_opp h.
Qed.
(** Source for [quotient_rel_trans]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_rel_trans : transitive quotient_rel.
Proof.
move=> y x z /asboolP hxy /asboolP hyz; apply/asboolP.
have := subspace_add hxy hyz.
by rewrite addrA subrK.
Qed.

Canonical quotient_equiv :=
  EquivRel quotient_rel quotient_rel_refl quotient_rel_sym quotient_rel_trans.
(** Source for [module_quotient]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition module_quotient := {eq_quot quotient_rel}.
HB.instance Definition _ := Choice.copy module_quotient {eq_quot quotient_rel}.
(** Source for [quotient_projection]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition quotient_projection (x : M) : module_quotient := \pi_module_quotient x.

(** Source for [quotient_projection_eq]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_projection_eq x y :
  quotient_projection x = quotient_projection y <-> S (x - y).
Proof.
split=> h.
  apply/asboolP.
  apply/(eqmodP quotient_equiv).
  exact: h.
apply/(eqmodP quotient_equiv)/asboolP.
exact: h.
Qed.

(** Source for [quotient_projection_surjective]: Federer (1969), 1.1.1, p.
    9, existence proof, from the definition of F to the quotient F/G. In
    words: Take finitely supported functions on the Cartesian product and
    quotient by the linearity relations in every argument. Supporting lemma
    for this passage; not separately stated in the book. *)
Lemma quotient_projection_surjective (q : module_quotient) :
  quotient_projection (repr q) = q.
Proof. exact: reprK. Qed.

(** Source for [quotient_add_compatible]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_add_compatible x y x' y' :
  quotient_projection x = quotient_projection x' ->
  quotient_projection y = quotient_projection y' ->
  quotient_projection (x + y) = quotient_projection (x' + y').
Proof.
move/quotient_projection_eq=> hx; move/quotient_projection_eq=> hy.
apply/quotient_projection_eq; rewrite opprD addrACA.
exact: subspace_add hx hy.
Qed.

(** Source for [quotient_scale_compatible]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_scale_compatible a x y :
  quotient_projection x = quotient_projection y ->
  quotient_projection (a *: x) = quotient_projection (a *: y).
Proof.
move/quotient_projection_eq=> h; apply/quotient_projection_eq.
rewrite -scalerBr; exact: subspace_scale h.
Qed.

(** Source for [quotient_opp_compatible]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_opp_compatible x y :
  quotient_projection x = quotient_projection y ->
  quotient_projection (- x) = quotient_projection (- y).
Proof.
by move=> h; rewrite -!scaleN1r; exact: quotient_scale_compatible h.
Qed.

(** Source for [quotient_zero]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition quotient_zero := quotient_projection 0.
(** Source for [quotient_add]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition quotient_add (x y : module_quotient) :=
  quotient_projection (repr x + repr y).
(** Source for [quotient_opp]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition quotient_opp (x : module_quotient) :=
  quotient_projection (- repr x).
(** Source for [quotient_scale]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition quotient_scale a (x : module_quotient) :=
  quotient_projection (a *: repr x).

(** Source for [quotient_addE]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_addE x y :
  quotient_add (quotient_projection x) (quotient_projection y) =
  quotient_projection (x + y).
Proof.
apply: quotient_add_compatible; exact: quotient_projection_surjective.
Qed.
(** Source for [quotient_oppE]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_oppE x :
  quotient_opp (quotient_projection x) = quotient_projection (- x).
Proof. apply: quotient_opp_compatible; exact: quotient_projection_surjective. Qed.
(** Source for [quotient_scaleE]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_scaleE a x :
  quotient_scale a (quotient_projection x) = quotient_projection (a *: x).
Proof. apply: quotient_scale_compatible; exact: quotient_projection_surjective. Qed.

(** Source for [quotient_addA]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_addA : associative quotient_add.
Proof.
move=> x y z; rewrite -[x]quotient_projection_surjective
  -[y]quotient_projection_surjective -[z]quotient_projection_surjective.
by rewrite !quotient_addE addrA.
Qed.
(** Source for [quotient_addC]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_addC : commutative quotient_add.
Proof. by move=> x y; rewrite /quotient_add addrC. Qed.
(** Source for [quotient_add0]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_add0 : left_id quotient_zero quotient_add.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective.
by rewrite /quotient_zero quotient_addE add0r.
Qed.
(** Source for [quotient_addN]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_addN : left_inverse quotient_zero quotient_opp quotient_add.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective.
by rewrite quotient_oppE quotient_addE addNr.
Qed.

HB.instance Definition _ := GRing.isZmodule.Build module_quotient
  quotient_addA quotient_addC quotient_add0 quotient_addN.

(** Source for [quotient_scaleA]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_scaleA a b x :
  quotient_scale a (quotient_scale b x) = quotient_scale (a * b) x.
Proof.
rewrite -[x]quotient_projection_surjective.
by rewrite !quotient_scaleE scalerA.
Qed.
(** Source for [quotient_scale1]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_scale1 : left_id 1 quotient_scale.
Proof. by move=> x; rewrite /quotient_scale scale1r quotient_projection_surjective. Qed.
(** Source for [quotient_scaleDr]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_scaleDr a : {morph quotient_scale a : x y / x + y}.
Proof.
move=> x y.
change (quotient_scale a (quotient_add x y) =
  quotient_add (quotient_scale a x) (quotient_scale a y)).
rewrite {1}/quotient_add quotient_scaleE scalerDr.
by rewrite /quotient_scale -quotient_addE.
Qed.
(** Source for [quotient_scaleDl]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_scaleDl x : {morph quotient_scale^~ x : a b / a + b}.
Proof.
move=> a b.
change (quotient_scale (a + b) x = quotient_add (quotient_scale a x) (quotient_scale b x)).
by rewrite /quotient_scale quotient_addE scalerDl.
Qed.
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build K module_quotient
  quotient_scaleA quotient_scale1 quotient_scaleDr quotient_scaleDl.

(** Source for [quotient_projection_linear]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_projection_linear : linear quotient_projection.
Proof.
move=> a x y.
change (quotient_projection (a *: x + y) =
  quotient_add (quotient_scale a (quotient_projection x)) (quotient_projection y)).
by rewrite quotient_scaleE quotient_addE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K M module_quotient
  *:%R quotient_projection quotient_projection_linear.

Section Factorisation.
Variable Z : lmodType K.
Variable f : {linear M -> Z}.
Hypothesis kills : forall x, S x -> f x = 0.

(** Retaining [kills] as a parameter lets canonical inference select the
    linear structure proved below for this particular factorisation. *)
(** Source for [quotient_lift]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition quotient_lift (x : module_quotient) := let _ := kills in f (repr x).

(** Source for [quotient_liftE]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_liftE x : quotient_lift (quotient_projection x) = f x.
Proof.
apply/eqP; rewrite -subr_eq0 -linearB /=.
apply/eqP/kills/quotient_projection_eq.
exact: quotient_projection_surjective.
Qed.

(** Source for [quotient_lift_linear]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_lift_linear : linear quotient_lift.
Proof.
move=> a x y; rewrite -[x]quotient_projection_surjective -[y]quotient_projection_surjective.
by rewrite -linearP !quotient_liftE linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K module_quotient Z
  *:%R quotient_lift quotient_lift_linear.

(** Source for [quotient_lift_unique]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma quotient_lift_unique (g : {linear module_quotient -> Z}) :
  (forall x, g (quotient_projection x) = f x) -> forall x, g x = quotient_lift x.
Proof.
by move=> e x; rewrite -[x]quotient_projection_surjective e quotient_liftE.
Qed.
End Factorisation.
End Quotient.
