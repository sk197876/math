(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear GradedAlgebra GradedSums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section ProjectionBounds.
Variable K : fieldType.
Variable V : lmodType K.
Variable P : nat -> {linear V -> V}.
Hypothesis hP : forall m n x, P m (P n x) = if m == n then P n x else 0.
(** Source for [projection_tail]: Federer (1969), 1.2.2, p. 11, opening
    displayed total-degree decomposition. In words: The homogeneous summand
    of total degree m is the direct sum of the tensors of degrees p and q
    with p+q=m. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma projection_tail x N : x = \sum_(i < N) P i x ->
  forall n, (N <= n)%N -> P n x = 0.
Proof.
move=> hx n hn; rewrite {1}hx linear_sum /=.
apply: big1 => i _; rewrite hP.
have hni : n != i by apply/eqP=> e; move: (ltn_ord i); rewrite -e ltnNge hn.
by rewrite (negPf hni).
Qed.
(** Source for [projection_reconstruct_widen]: Federer (1969), 1.2.2, p. 11,
    opening displayed total-degree decomposition. In words: The homogeneous
    summand of total degree m is the direct sum of the tensors of degrees p
    and q with p+q=m. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma projection_reconstruct_widen x N M : x = \sum_(i < N) P i x ->
  (N <= M)%N -> x = \sum_(i < M) P i x.
Proof.
move=> hx hNM; rewrite {1}hx (big_ord_widen M (fun i : nat => P i x) hNM) big_mkcond.
apply: eq_bigr => i _; case: ifP => hi //.
by rewrite (projection_tail hx) // leqNgt hi.
Qed.
End ProjectionBounds.

Section TensorHomogeneous.
Variable K : fieldType.
Variables A B : lmodType K.
Variables (GA : grading A) (GB : grading B).

(** Source for [tensor_homogeneous_induction]: Federer (1969), 1.2.2, p. 11,
    opening displayed total-degree decomposition. In words: The homogeneous
    summand of total degree m is the direct sum of the tensors of degrees p
    and q with p+q=m. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_homogeneous_induction (P : tensor_space A B -> Prop)
  (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
  (hZ : forall a x, P x -> P (a *: x))
  (hh : forall p q a b, homogeneous GA p a -> homogeneous GB q b -> P (tensor_inj a b)) :
  forall x, P x.
Proof.
apply: tensor_induction => // a b.
move: a; apply: (graded_induction (G := GA)) => [|a a' ha ha'|p a ha].
- by rewrite tensor_inj0l.
- rewrite tensor_inj_addl; exact: hD ha ha'.
move: b; apply: (graded_induction (G := GB)) => [|b b' hb hb'|q b hb].
- by rewrite tensor_inj0r.
- rewrite tensor_inj_addr; exact: hD hb hb'.
exact: hh ha hb.
Qed.

(** Source for [tensor_grade_fun]: Federer (1969), 1.2.2, p. 11, opening
    displayed total-degree decomposition. In words: The homogeneous summand
    of total degree m is the direct sum of the tensors of degrees p and q
    with p+q=m. Definition or construction used to formalise this passage. *)
Definition tensor_grade_fun n (x : tensor_space A B) :=
  \sum_(i < n.+1) tensor_map (grade GA i) (grade GB (n-i)) x.
(** Source for [tensor_grade_linear]: Federer (1969), 1.2.2, p. 11, opening
    displayed total-degree decomposition. In words: The homogeneous summand
    of total degree m is the direct sum of the tensors of degrees p and q
    with p+q=m. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_grade_linear n : linear (tensor_grade_fun n).
Proof.
move=> a x y; rewrite /tensor_grade_fun scaler_sumr -big_split /=.
by apply: eq_bigr => i _; rewrite linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build K (tensor_space A B) (tensor_space A B)
  *:%R (tensor_grade_fun n) (tensor_grade_linear n).
(** Source for [tensor_grade]: Federer (1969), 1.2.2, p. 11, opening
    displayed total-degree decomposition. In words: The homogeneous summand
    of total degree m is the direct sum of the tensors of degrees p and q
    with p+q=m. Definition or construction used to formalise this passage. *)
Definition tensor_grade n : {linear tensor_space A B -> tensor_space A B} :=
  GRing.Linear.clone _ _ _ _ (tensor_grade_fun n) _.

(** Source for [tensor_grade_pure]: Federer (1969), 1.2.2, p. 11, opening
    displayed total-degree decomposition. In words: The homogeneous summand
    of total degree m is the direct sum of the tensors of degrees p and q
    with p+q=m. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma tensor_grade_pure n p q a b : homogeneous GA p a -> homogeneous GB q b ->
  tensor_grade n (tensor_inj a b) = if p+q == n then tensor_inj a b else 0.
Proof.
move=> ha hb; rewrite /tensor_grade /tensor_grade_fun /=.
under eq_bigr do rewrite tensor_mapE (grade_homogeneous _ ha).
have he i : tensor_inj (if i == p then a else 0) (grade GB (n-i) b) =
    if i == p then tensor_inj a (grade GB (n-i) b) else 0.
  by case: ifP=> _; rewrite ?tensor_inj0l.
under eq_bigr do rewrite he.
rewrite -big_mkcond.
case: (ltnP p n.+1) => hp.
  rewrite (big_pred1 (Ordinal hp)); last by [].
  rewrite (grade_homogeneous _ hb).
  have eqn : (n-p == q)%N = (p+q == n)%N.
    apply/eqP/eqP=> e.
      by rewrite -e subnKC.
    by rewrite -e addKn.
  rewrite eqn; by case: ifP=> _; rewrite ?tensor_inj0r.
have hn : (p+q != n)%N.
  apply/eqP=> e; have := leq_trans hp (leq_addr q p).
  by rewrite e ltnn.
rewrite (negPf hn); apply: big1 => i /eqP hip.
by move: (ltn_ord i); rewrite hip ltnNge hp.

Qed.

(** Source for [tensor_grade_orthogonal]: Federer (1969), 1.2.2, p. 11,
    opening displayed total-degree decomposition. In words: The homogeneous
    summand of total degree m is the direct sum of the tensors of degrees p
    and q with p+q=m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_grade_orthogonal m n x : tensor_grade m (tensor_grade n x) =
  if m == n then tensor_grade n x else 0.
Proof.
elim/tensor_homogeneous_induction: x => [|x y hx hy|a x hx|p q a b ha hb].
- by rewrite !linear0; case: ifP.
- rewrite !linearD /= hx hy; by case: ifP; rewrite ?addr0.
- rewrite !linearZ /= hx; by case: ifP; rewrite ?scaler0.
rewrite (tensor_grade_pure n ha hb); case he: (p+q == n).
  move/eqP: he => <-; rewrite (tensor_grade_pure m ha hb) eq_sym.
  by [].
by rewrite linear0; case: ifP.
Qed.

(** Source for [tensor_grade_finite]: Federer (1969), 1.2.2, p. 11, opening
    displayed total-degree decomposition. In words: The homogeneous summand
    of total degree m is the direct sum of the tensors of degrees p and q
    with p+q=m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_grade_finite x : exists N, x = \sum_(i < N) tensor_grade i x.
Proof.
elim/tensor_homogeneous_induction: x => [|x y [N hx] [M hy]|a x [N hx]|p q a b ha hb].
- exists 0%N; by rewrite big_ord0.
- exists (maxn N M).
  have hx' := projection_reconstruct_widen tensor_grade_orthogonal hx (leq_maxl N M).
  have hy' := projection_reconstruct_widen tensor_grade_orthogonal hy (leq_maxr N M).
  under eq_bigr do rewrite linearD.
  by rewrite big_split /= -hx' -hy'.
- exists N; under eq_bigr do rewrite linearZ.
  by rewrite -scaler_sumr -hx.
exists (p+q).+1.
under eq_bigr do rewrite (tensor_grade_pure _ ha hb) eq_sym.
rewrite -big_mkcond.
by rewrite (big_pred1 (Ordinal (ltnSn (p+q)))).
Qed.

(** Source for [tensor_grading_product]: Federer (1969), 1.2.2, p. 11,
    opening displayed total-degree decomposition. In words: The homogeneous
    summand of total degree m is the direct sum of the tensors of degrees p
    and q with p+q=m. Definition or construction used to formalise this
    passage. *)
Definition tensor_grading_product : grading (tensor_space A B) :=
  @Grading K (tensor_space A B) tensor_grade tensor_grade_orthogonal tensor_grade_finite.
(** Source for [tensor_homogeneous_pure]: Federer (1969), 1.2.2, p. 11,
    opening displayed total-degree decomposition. In words: The homogeneous
    summand of total degree m is the direct sum of the tensors of degrees p
    and q with p+q=m. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma tensor_homogeneous_pure p q a b : homogeneous GA p a -> homogeneous GB q b ->
  homogeneous tensor_grading_product (p+q) (tensor_inj a b).
Proof. by move=> ha hb; rewrite /homogeneous /= (tensor_grade_pure _ ha hb) eqxx. Qed.
End TensorHomogeneous.

Section ComponentInduction.
Variable K : fieldType.
Variables A B : lmodType K.
Variables (GA : grading A) (GB : grading B).
(** Source for [tensor_component_induction]: Federer (1969), 1.2.2, p. 11,
    opening displayed total-degree decomposition. In words: The homogeneous
    summand of total degree m is the direct sum of the tensors of degrees p
    and q with p+q=m. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma tensor_component_induction n (P : tensor_space A B -> Prop)
  (h0 : P 0) (hD : forall x y, P x -> P y -> P (x+y))
  (hZ : forall a x, P x -> P (a *: x))
  (hh : forall p q a b, (p+q = n)%N -> homogeneous GA p a -> homogeneous GB q b -> P (tensor_inj a b)) :
  forall x, homogeneous (tensor_grading_product GA GB) n x -> P x.
Proof.
move=> x hx; rewrite -hx; clear hx.
elim/(tensor_homogeneous_induction (GA := GA) (GB := GB)): x => [|x y hx' hy|a x hx'|p q a b ha hb].
- by rewrite /grade /= linear0.
- rewrite /grade /= linearD; exact: hD hx' hy.
- rewrite /grade /= linearZ; exact: hZ hx'.
change (P (tensor_grade GA GB n (tensor_inj a b))).
rewrite (tensor_grade_pure n ha hb); case e: (p+q == n)%N => //.
exact: hh (eqP e) ha hb.
Qed.
End ComponentInduction.

Section HomogeneousExtensionality.
Variable K : fieldType.
Variables A B C D Z : lmodType K.
Variables (GA : grading A) (GB : grading B) (GC : grading C) (GD : grading D).
Variables f g : tensor_space A B -> tensor_space C D -> Z.
Hypotheses (hf : bilinear f) (hg : bilinear g).
(** Source for [tensor_homogeneous_bilinear_ext]: Federer (1969), 1.2.2, p.
    11, opening displayed total-degree decomposition. In words: The
    homogeneous summand of total degree m is the direct sum of the tensors
    of degrees p and q with p+q=m. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tensor_homogeneous_bilinear_ext :
  (forall p q r t a b c d, homogeneous GA p a -> homogeneous GB q b ->
    homogeneous GC r c -> homogeneous GD t d ->
    f (tensor_inj a b) (tensor_inj c d) = g (tensor_inj a b) (tensor_inj c d)) ->
  forall x y, f x y = g x y.
Proof.
move=> e; apply: (tensor_homogeneous_induction (GA := GA) (GB := GB))
  => [y|x x' hx hx' y|k x hx y|p q a b ha hb].
- by rewrite (bil0l hf) (bil0l hg).
- by rewrite (bilDl hf) (bilDl hg) hx hx'.
- by rewrite (bilZl hf) (bilZl hg) hx.
apply: (tensor_homogeneous_induction (GA := GC) (GB := GD))
  => [|y y' hy hy'|k y hy|r t c d hc hd].
- by rewrite (bil0r hf) (bil0r hg).
- by rewrite (bilDr hf) (bilDr hg) hy hy'.
- by rewrite (bilZr hf) (bilZr hg) hy.
exact: e ha hb hc hd.
Qed.
End HomogeneousExtensionality.
