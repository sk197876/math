(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP Bilinear GradedAlgebra GradedSums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Signs.
Variable K : fieldType.
(** Source for [koszul]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Definition
    or construction used to formalise this passage. *)
Definition koszul (s : bool) (p q : nat) : K := if s then (-1)^+(p*q) else 1.
(** Source for [koszulC]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma koszulC s p q : koszul s p q = koszul s q p.
Proof. by rewrite /koszul mulnC. Qed.
(** Source for [koszul0l]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma koszul0l s q : koszul s 0 q = 1.
Proof. by rewrite /koszul mul0n expr0; case: s. Qed.
(** Source for [koszul0r]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma koszul0r s p : koszul s p 0 = 1.
Proof. by rewrite koszulC koszul0l. Qed.
(** Source for [koszulDl]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma koszulDl s p q r : koszul s (p+q) r = koszul s p r * koszul s q r.
Proof. by rewrite /koszul mulnDl exprD; case: s; rewrite ?mul1r. Qed.
(** Source for [koszulDr]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma koszulDr s p q r : koszul s p (q+r) = koszul s p q * koszul s p r.
Proof. by rewrite koszulC koszulDl ![koszul s _ p]koszulC. Qed.
(** Source for [koszul_square]: Federer (1969), 1.2.1, p. 11, final
    displayed anticommutative law. In words: Interchanging homogeneous
    factors of degrees m and n multiplies the product by the sign (-1)^(mn).
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma koszul_square s p q : koszul s p q * koszul s p q = 1.
Proof. by rewrite /koszul; case: s; rewrite ?mul1r // -expr2 sqrr_sign. Qed.
End Signs.

Section DegreeSigns.
Variable K : fieldType.
Variable V : lmodType K.
Variable G : grading V.
(** Source for [scalar_map]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Definition
    or construction used to formalise this passage. *)
Definition scalar_map (a : K) : {linear V -> V} :=
  GRing.Linear.clone _ _ _ _ ( *:%R a) _.
(** Source for [degree_sign]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Definition
    or construction used to formalise this passage. *)
Definition degree_sign (s : bool) q :=
  graded_sum G (fun p => scalar_map (koszul K s q p)).
HB.instance Definition _ s q := GRing.Linear.copy (degree_sign s q)
  (graded_sum G (fun p => scalar_map (koszul K s q p))).
(** Source for [degree_signE]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma degree_signE s p q x : homogeneous G p x ->
  degree_sign s q x = koszul K s q p *: x.
Proof. move=> hx; exact: graded_sum_homogeneous hx. Qed.
End DegreeSigns.

Section SignIdentities.
Variable K : fieldType.
(** Source for [koszul_parity]: Federer (1969), 1.2.1, p. 11, final
    displayed anticommutative law. In words: Interchanging homogeneous
    factors of degrees m and n multiplies the product by the sign (-1)^(mn).
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma koszul_parity s p q :
  koszul K s p q = if s && odd p && odd q then -1 else 1.
Proof.
case: s; rewrite /koszul //= -signr_odd oddM.
by case: (odd p); case: (odd q).
Qed.
(** Source for [koszul_cocycle]: Federer (1969), 1.2.1, p. 11, final
    displayed anticommutative law. In words: Interchanging homogeneous
    factors of degrees m and n multiplies the product by the sign (-1)^(mn).
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma koszul_cocycle s p q r t :
  koszul K s p q * koszul K s (p+r) t =
  koszul K s r t * koszul K s p (q+t).
Proof.
rewrite !koszul_parity !oddD.
case: s => /=; last by rewrite !mul1r.
by case: (odd p); case: (odd q); case: (odd r); case: (odd t);
  rewrite /= ?mul1r ?mulr1 ?mulN1r ?mulrN1 ?opprK.
Qed.
(** Source for [koszul_braid]: Federer (1969), 1.2.1, p. 11, final displayed
    anticommutative law. In words: Interchanging homogeneous factors of
    degrees m and n multiplies the product by the sign (-1)^(mn). Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma koszul_braid s p q r t :
  koszul K s q r * koszul K s (p+r) (q+t) =
  (koszul K s p q * koszul K s r t) * koszul K s p t.
Proof.
rewrite !koszul_parity !oddD.
case: s => /=; last by rewrite !mul1r.
by case: (odd p); case: (odd q); case: (odd r); case: (odd t);
  rewrite /= ?mul1r ?mulr1 ?mulN1r ?mulrN1 ?opprK.
Qed.
(** Source for [koszul_anticomm]: Federer (1969), 1.2.1, p. 11, final
    displayed anticommutative law. In words: Interchanging homogeneous
    factors of degrees m and n multiplies the product by the sign (-1)^(mn).
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma koszul_anticomm p q r t :
  koszul K true q r * (koszul K true p r * koszul K true q t) =
  koszul K true (p+q) (r+t) * koszul K true t p.
Proof.
rewrite !koszul_parity !oddD /=.
by case: (odd p); case: (odd q); case: (odd r); case: (odd t);
  rewrite /= ?mul1r ?mulr1 ?mulN1r ?mulrN1 ?opprK.
Qed.
End SignIdentities.

(** Source for [degree_sign_false]: Federer (1969), 1.2.1, p. 11, final
    displayed anticommutative law. In words: Interchanging homogeneous
    factors of degrees m and n multiplies the product by the sign (-1)^(mn).
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma degree_sign_false (K : fieldType) (V : lmodType K) (G : grading V) q x :
  degree_sign G false q x = x.
Proof.
elim/(graded_induction (G:=G)): x => [|x y hx hy|p x hx].
- exact: linear0.
- by rewrite linearD /= hx hy.
by rewrite (degree_signE false q hx) /koszul scale1r.
Qed.
