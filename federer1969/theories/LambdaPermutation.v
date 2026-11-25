(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import AlternatingAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.4.3: two increasing index tuples can be related by a
    permutation only when the tuples agree and the permutation is the
    identity. This is the combinatorial step in the off-diagonal pairing. *)
(** Source for [Lambda_tnth_injective]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Lambda_tnth_injective n m (lambda : Lambda n m) : injective (tnth (val lambda)).
Proof.
apply/tuple_uniqP; have h := sorted_uniq ltn_trans ltnn (valP lambda).
by rewrite (map_inj_uniq val_inj) in h.
Qed.
(** Source for [Lambda_permutation_identity]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma Lambda_permutation_identity n m (lambda mu : Lambda n m) (sigma : 'S_m) :
  (forall i, tnth (val lambda) i = tnth (val mu) (sigma i)) -> lambda = mu /\ sigma = 1%g.
Proof.
move=> h.
have hp : perm_eq (permutation_sequence sigma) (enum 'I_m).
  apply: uniq_perm; [exact: permutation_sequence_uniq | exact: enum_uniq |].
  by move=> i; rewrite permutation_sequence_mem mem_enum.
have hs : val (val lambda) = map (tnth (val mu)) (permutation_sequence sigma).
  rewrite -[LHS]map_tnth_enum -(map_comp (tnth (val mu)) sigma (enum 'I_m)).
  apply: eq_map => i; exact: h.
have hv : map val (val lambda) = map val (val mu).
  apply: (irr_sorted_eq ltn_trans ltnn (valP lambda) (valP mu)).
  apply: perm_mem; apply: perm_map.
  rewrite hs -(map_tnth_enum (val mu)); exact: perm_map hp.
have hl : lambda = mu.
  apply: val_inj; apply: val_inj; exact (inj_map val_inj hv).
split=> //; apply/permP=> i; rewrite perm1; apply (@Lambda_tnth_injective n m mu (sigma i) i).
have hi := h i; rewrite hl in hi; exact (esym hi).
Qed.
(** Source for [Lambda_permutation_delta]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma Lambda_permutation_delta n m (lambda mu : Lambda n m) (sigma : 'S_m) :
  all (fun i => tnth (val lambda) i == tnth (val mu) (sigma i)) (enum 'I_m) =
    ((lambda == mu) && (sigma == 1%g)).
Proof.
apply/idP/idP.
- move/allP=> h; have hp i : tnth (val lambda) i = tnth (val mu) (sigma i).
    apply/eqP; apply: h; by rewrite mem_enum.
  have [-> ->] := Lambda_permutation_identity hp; by rewrite !eqxx.
- move/andP=> [/eqP -> /eqP ->]; apply/allP=> i _; by rewrite perm1 eqxx.
Qed.
