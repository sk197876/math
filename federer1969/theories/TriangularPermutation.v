(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.2, the triangular special case: every nonidentity
    permutation moves some index to an earlier position. *)
(** Source for [permutation_ge_identity]: Federer (1969), 1.4.2, p. 19, last
    sentence, the triangular special case. In words: If the i-th one-form
    vanishes on every earlier vector, the product evaluates to the ordered
    product of the diagonal values. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma permutation_ge_identity n (sigma : 'S_n) :
  (forall i : 'I_n, i <= sigma i) -> sigma = 1%g.
Proof.
move=> hge.
have hs : \sum_(i : 'I_n) (sigma i : nat) = \sum_(i : 'I_n) (i : nat).
  by rewrite [RHS](reindex sigma (onW_bij _ (injF_bij (perm_inj (s:=sigma))))) .
have hle := @leqif_sum (Finite.clone 'I_n _) predT (fun i => (i : nat) == sigma i)
  (fun i => (i : nat)) (fun i => (sigma i : nat)) (fun i _ => leqif_eq (hge i)).
have he := eq_leqif hle.
rewrite hs eqxx in he.
apply/permP=> i; rewrite perm1; apply: val_inj.
have hi := elimT forallP (esym he) i.
by move: hi; rewrite implyTb eq_sym => /eqP.
Qed.
(** Source for [permutation_lower]: Federer (1969), 1.4.2, p. 19, last
    sentence, the triangular special case. In words: If the i-th one-form
    vanishes on every earlier vector, the product evaluates to the ordered
    product of the diagonal values. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma permutation_lower n (sigma : 'S_n) : sigma != 1%g ->
  exists i : 'I_n, sigma i < i.
Proof.
move=> hne; have [/existsP h|/existsPn hn] := boolP [exists i : 'I_n, sigma i < i].
- exact: h.
- have he : sigma = 1%g.
    apply: permutation_ge_identity => i; have hi := hn i.
    by move: hi; rewrite -leqNgt.
  by rewrite he eqxx in hne.
Qed.
