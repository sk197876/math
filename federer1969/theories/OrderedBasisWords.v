(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import GrassmannTrace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.5.2: ordering products of basis vectors contributes
    precisely the inversion sign already defined in 1.3.3. *)
(** Source for [exterior_index_word_order]: Federer (1969), 1.5.2, p. 22,
    the two inclusion cases and the definitions of M and N. In words: A
    basis interior product vanishes unless the contracted index set is
    contained in the other; otherwise it is the complementary basis product
    with the appropriate crossing-count sign. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma exterior_index_word_order (K : fieldType) (V : lmodType K) n
  (e : 'I_n -> V) (s t : seq 'I_n) :
  sorted leq (map val t) -> perm_eq s t ->
  exterior_word [seq e i | i <- s] =
    (-1 : K)^+(inversions (map val s)) *: exterior_word [seq e i | i <- t].
Proof.
move=> ht hp; pose f := nth 0 [seq e i | i <- enum 'I_n].
have hf (i : 'I_n) : f (val i) = e i.
  by rewrite /f (nth_map i) ?size_enum_ord ?(valP i) // nth_ord_enum.
have hm (u : seq 'I_n) : [seq f i | i <- map val u] = [seq e i | i <- u].
  rewrite -map_comp; apply: eq_map => i; exact: hf.
have ho : order_indices (map val s) = map val t.
  apply: order_indices_eq ht _; exact: perm_map hp.
have h := exterior_word_order f (map val s).
by rewrite ho !hm in h.
Qed.
(** Source for [tuple_Lambda_order]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma tuple_Lambda_order n m (s : m.-tuple 'I_n) : uniq s ->
  exists lambda : Lambda n m, perm_eq s (val lambda).
Proof.
move=> hu; have hc : #|[set i in s]| = m.
  by rewrite cardsE (card_uniqP hu) size_tuple.
have [lambda hl] := Lambda_set_surjective hc.
exists lambda; apply: uniq_perm; [exact: hu|exact: Lambda_uniq|].
move=> i; have hi := congr1 (fun S : {set 'I_n} => i \in S) hl.
by rewrite /Lambda_set !inE in hi.
Qed.

(** Federer 1.5.2: a covector basis product evaluates an arbitrary
    ordered tuple as its permutation sign, or zero if the indices differ. *)
Section BasisWordPairing.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n m : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
(** Source for [basis_word_pairing]: Federer (1969), 1.5.2, p. 22, the two
    inclusion cases and the definitions of M and N. In words: A basis
    interior product vanishes unless the contracted index set is contained
    in the other; otherwise it is the complementary basis product with the
    appropriate crossing-count sign. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem basis_word_pairing (s : m.-tuple 'I_n) (mu : Lambda n m) :
  form_include (omega_lambda h2 omega mu) (exterior_word [seq e i | i <- s]) =
    if perm_eq s (val mu) then (-1 : K)^+(inversions (map val s)) else 0.
Proof.
case hu : (uniq s).
- have [lambda hp] := tuple_Lambda_order hu.
  have hs : sorted leq (map val (val lambda)).
    have := valP lambda; by rewrite ltn_sorted_uniq_leq => /andP [].
  rewrite (exterior_index_word_order e hs hp) linearZ.
  change ((-1 : K)^+(inversions (map val s)) *
      pairing (e_lambda e (val lambda)) (omega_lambda h2 omega mu) =
    if perm_eq s (val mu) then (-1 : K)^+(inversions (map val s)) else 0).
  rewrite (pairing_e_omega h2 hdual).
  have he : perm_eq s (val mu) = (mu == lambda).
    apply/idP/idP.
    + move=> hp'; apply/eqP; symmetry; apply: Lambda_perm_equal.
      have hps : perm_eq (val lambda) s by rewrite perm_sym.
      exact: perm_trans hps hp'.
    + move/eqP=> ->; exact: hp.
  by rewrite he; case: (mu == lambda); rewrite ?mulr1 ?mulr0.
- have hn : ~~ perm_eq s (val mu).
    apply/negP=> hp; move: hu; by rewrite (perm_uniq hp) Lambda_uniq.
  by rewrite (negbTE hn) (exterior_word_map_nonuniq e (negbT hu)) linear0.
Qed.
End BasisWordPairing.
