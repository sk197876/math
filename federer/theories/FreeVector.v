(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

(** Finitely supported functions, with their pointwise vector-space structure. *)
Section FreeVector.
Variable K : fieldType.
Variable A : choiceType.

(** Source for [free_vector]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_vector := {fsfun A -> K with 0}.
HB.instance Definition _ := Choice.copy free_vector {fsfun A -> K with 0}.

(** Source for [free_zero]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_zero : free_vector := [fsfun with 0].
(** Source for [free_opp]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_opp (f : free_vector) : free_vector :=
  [fsfun x in finsupp f => - f x | 0].
(** Source for [free_add]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_add (f g : free_vector) : free_vector :=
  [fsfun x in finsupp f `|` finsupp g => f x + g x | 0].
(** Source for [free_scale]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_scale (a : K) (f : free_vector) : free_vector :=
  [fsfun x in finsupp f => a * f x | 0].

(** Source for [free_zeroE]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_zeroE x : free_zero x = 0.
Proof. exact: fsfun0E. Qed.
(** Source for [free_oppE]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_oppE f x : free_opp f x = - f x.
Proof.
rewrite /free_opp fsfunE; case: ifP=> // hx.
by rewrite fsfun_dflt ?hx // oppr0.
Qed.
(** Source for [free_addE]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_addE f g x : free_add f g x = f x + g x.
Proof.
rewrite /free_add fsfunE; case: ifP=> //.
move=> hx; have hnot : x \notin (finsupp f `|` finsupp g) by rewrite hx.
rewrite inE in hnot; move/norP: hnot => [hf hg].
by rewrite (fsfun_dflt hf) (fsfun_dflt hg) add0r.
Qed.
(** Source for [free_scaleE]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_scaleE a f x : free_scale a f x = a * f x.
Proof.
rewrite /free_scale fsfunE; case: ifP=> // hx.
by rewrite fsfun_dflt ?hx // mulr0.
Qed.

(** Source for [free_addA]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_addA : associative free_add.
Proof. by move=> f g h; apply/fsfunP=> x; rewrite !free_addE addrA. Qed.
(** Source for [free_addC]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_addC : commutative free_add.
Proof. by move=> f g; apply/fsfunP=> x; rewrite !free_addE addrC. Qed.
(** Source for [free_add0]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_add0 : left_id free_zero free_add.
Proof. by move=> f; apply/fsfunP=> x; rewrite free_addE free_zeroE add0r. Qed.
(** Source for [free_addN]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_addN : left_inverse free_zero free_opp free_add.
Proof.
by move=> f; apply/fsfunP=> x; rewrite free_addE free_oppE free_zeroE addNr.
Qed.

HB.instance Definition _ := GRing.isNmodule.Build free_vector
  free_addA free_addC free_add0.
HB.instance Definition _ := GRing.Nmodule_isZmodule.Build free_vector free_addN.

(** Source for [free_scaleA]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_scaleA a b f :
  free_scale a (free_scale b f) = free_scale (a * b) f.
Proof. by apply/fsfunP=> x; rewrite !free_scaleE mulrA. Qed.
(** Source for [free_scale1]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_scale1 : left_id 1 free_scale.
Proof. by move=> f; apply/fsfunP=> x; rewrite free_scaleE mul1r. Qed.
(** Source for [free_scaleDr]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_scaleDr a : {morph free_scale a : f g / f + g}.
Proof. by move=> f g; apply/fsfunP=> x; rewrite !free_addE !free_scaleE !free_addE mulrDr. Qed.
(** Source for [free_scaleDl]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_scaleDl f : {morph free_scale^~ f : a b / a + b}.
Proof. by move=> a b; apply/fsfunP=> x; rewrite !free_addE !free_scaleE mulrDl. Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build K free_vector
  free_scaleA free_scale1 free_scaleDr free_scaleDl.

(** Source for [free_eval]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_eval x (f : free_vector) : K^o := f x.
(** Source for [free_eval_linear]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_eval_linear x : linear (free_eval x).
Proof. by move=> a f g; rewrite /free_eval free_addE free_scaleE. Qed.
HB.instance Definition _ x := GRing.isLinear.Build K free_vector K^o
  *:%R (free_eval x) (free_eval_linear x).

(** Source for [delta]: Federer (1969), 1.1.1, p. 9, existence proof, from
    the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition delta (a : A) : free_vector := [fsfun x in [fset a] => 1 | 0].
(** Source for [deltaE]: Federer (1969), 1.1.1, p. 9, existence proof, from
    the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma deltaE a x : delta a x = if x == a then 1 else 0.
Proof. by rewrite /delta fsfunE inE. Qed.

(** Source for [free_support_add]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_support_add f g :
  finsupp (f + g : free_vector) `<=` finsupp f `|` finsupp g.
Proof. exact: finsupp_sub. Qed.
(** Source for [free_support_scale]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_support_scale a f :
  finsupp (a *: f : free_vector) `<=` finsupp f.
Proof. exact: finsupp_sub. Qed.
(** Source for [delta_support]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma delta_support a : finsupp (delta a) `<=` [fset a].
Proof. exact: finsupp_sub. Qed.

Section Extension.
Variable Z : lmodType K.
Variable h : A -> Z.

(** Source for [free_extend]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition free_extend (f : free_vector) :=
  \sum_(x <- finsupp f) f x *: h x.

(** Source for [free_extend_on]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_extend_on f (S : {fset A}) : finsupp f `<=` S ->
  free_extend f = \sum_(x <- S) f x *: h x.
Proof.
move=> hS; rewrite /free_extend.
apply: big_fset_incl; first exact: hS.
move=> x _ hx.
by rewrite (fsfun_dflt hx) scale0r.
Qed.

(** Source for [free_extend_add]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_extend_add f g : free_extend (f + g) = free_extend f + free_extend g.
Proof.
rewrite (free_extend_on (free_support_add f g)).
rewrite (free_extend_on (fsubsetUl (finsupp f) (finsupp g))).
rewrite (free_extend_on (fsubsetUr (finsupp f) (finsupp g))).
rewrite -big_split /=; apply: eq_bigr => x _.
by rewrite free_addE scalerDl.
Qed.

(** Source for [free_extend_scale]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_extend_scale a f : free_extend (a *: f) = a *: free_extend f.
Proof.
rewrite (free_extend_on (free_support_scale a f)) /free_extend scaler_sumr.
apply: eq_bigr => x _; by rewrite free_scaleE scalerA.
Qed.

(** Source for [free_extend_linear]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_extend_linear : linear free_extend.
Proof. by move=> a f g; rewrite free_extend_add free_extend_scale. Qed.
HB.instance Definition _ := GRing.isLinear.Build K free_vector Z
  *:%R free_extend free_extend_linear.

(** Source for [free_extend_delta]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_extend_delta a : free_extend (delta a) = h a.
Proof.
by rewrite (free_extend_on (delta_support a)) big_seq_fset1 deltaE eqxx scale1r.
Qed.
End Extension.

(** Source for [free_expansion]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_expansion (f : free_vector) :
  f = \sum_(x <- finsupp f) f x *: delta x.
Proof.
apply/fsfunP=> x.
change (free_eval x f = free_eval x (\sum_(a <- finsupp f) f a *: delta a)).
rewrite linear_sum /=.
under eq_bigr do rewrite linearZ /= /free_eval deltaE.
case: (boolP (x \in finsupp f)) => hx.
  rewrite (big_fsetD1 x hx) eqxx /GRing.scale /= mulr1.
  rewrite big1_fset ?addr0 // => y.
  rewrite inE => /andP [hy _] _.
  rewrite inE in hy.
  by rewrite eq_sym (negPf hy) mulr0.
rewrite /free_eval (fsfun_dflt hx) big1_fset // => y hy _.
have hyx : y != x by apply: contraNneq hx => <-.
by rewrite eq_sym (negPf hyx) scaler0.
Qed.

(** Source for [free_linear_ext]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma free_linear_ext (Z : lmodType K) (f g : {linear free_vector -> Z}) :
  (forall a, f (delta a) = g (delta a)) -> forall t, f t = g t.
Proof.
move=> e t; rewrite (free_expansion t) !linear_sum /=.
apply: eq_bigr => x _; by rewrite !linearZ /= e.
Qed.
End FreeVector.
Arguments free_linear_ext {K A Z} f g _ t.
