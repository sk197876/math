(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import GrassmannTrace.
From Federer Require Import OrderedBasisWords.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: the same ordering calculation for products of
    covectors. Omega makes this the exterior calculation of 1.3.4. *)
Section CovectorWords.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n -> A_m V K^o 1.
(** Source for [covector_word]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Definition or construction used to
    formalise this passage. *)
Definition covector_word (s : seq 'I_n) :=
  Omega h2 V (exterior_word [seq one_hom (omega i) | i <- s]).
(** Source for [covector_word_Lambda]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma covector_word_Lambda m (lambda : Lambda n m) :
  covector_word (val lambda) = form_include (omega_lambda h2 omega lambda).
Proof.
have ho : (fun i => one_form (one_hom (omega i))) = omega.
  apply: funext => i; exact: one_homK.
have h := @Omega_e_lambda K h2 V n (fun i => one_hom (omega i)) m lambda.
rewrite ho in h.
rewrite /covector_word -(e_lambdaE (fun i => one_hom (omega i)) (val lambda)) -Omega_m_include h.
by [].
Qed.
(** Source for [covector_word_product]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma covector_word_product (s t : seq 'I_n) :
  alternating_wedge h2 (scalar_bilinear K) (covector_word s) (covector_word t) =
    covector_word (s++t).
Proof.
rewrite /covector_word.
apply: eq_trans (esym (algebra_map_mul (Omega h2 V) _ _)) _.
change (Omega h2 V (wedge (exterior_word [seq one_hom (omega i) | i <- s])
  (exterior_word [seq one_hom (omega i) | i <- t])) =
  Omega h2 V (exterior_word [seq one_hom (omega i) | i <- s++t])).
by rewrite exterior_word_cat map_cat.
Qed.
(** Source for [covector_word_nonuniq]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma covector_word_nonuniq s : ~~ uniq s -> covector_word s = 0.
Proof. move=> hs; by rewrite /covector_word (exterior_word_map_nonuniq _ hs) linear0. Qed.
(** Source for [covector_word_order]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma covector_word_order (s t : seq 'I_n) : sorted leq (map val t) -> perm_eq s t ->
  covector_word s = (-1 : K)^+(inversions (map val s)) *: covector_word t.
Proof.
move=> ht hp; rewrite /covector_word (exterior_index_word_order (fun i => one_hom (omega i)) ht hp).
exact: linearZ.
Qed.
Variable e : 'I_n -> V.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
(** Source for [covector_word_pairing]: Federer (1969), 1.5.2, p. 22, the
    two inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem covector_word_pairing m (s : m.-tuple 'I_n) (mu : Lambda n m) :
  covector_word s (exterior_word [seq e i | i <- val mu]) =
    if perm_eq s (val mu) then (-1 : K)^+(inversions (map val s)) else 0.
Proof.
case hu : (uniq s).
- have [lambda hp] := tuple_Lambda_order hu.
  have hs : sorted leq (map val (val lambda)).
    have := valP lambda; by rewrite ltn_sorted_uniq_leq => /andP [].
  rewrite (covector_word_order hs hp) hom_finite_scaleE covector_word_Lambda.
  change ((-1 : K)^+(inversions (map val s)) *
      pairing (e_lambda e (val mu)) (omega_lambda h2 omega lambda) =
    if perm_eq s (val mu) then (-1 : K)^+(inversions (map val s)) else 0).
  rewrite (pairing_e_omega h2 hdual).
  have he : perm_eq s (val mu) = (lambda == mu).
    apply/idP/idP.
    + move=> hp'; apply/eqP; apply: Lambda_perm_equal.
      have hps : perm_eq (val lambda) s by rewrite perm_sym.
      exact: perm_trans hps hp'.
    + move/eqP=> <-; exact: hp.
  by rewrite he; case: (lambda == mu); rewrite ?mulr1 ?mulr0.
- have hn : ~~ perm_eq s (val mu).
    apply/negP=> hp; move: hu; by rewrite (perm_uniq hp) Lambda_uniq.
  by rewrite (negbTE hn) (covector_word_nonuniq (negbT hu)) hom_finite_zeroE.
Qed.
End CovectorWords.
