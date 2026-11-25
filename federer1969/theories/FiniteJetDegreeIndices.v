(** Supporting Federer (1969), 3.4.8(5), p. 328:
    finite derivative coefficients indexed by the already proved
    monomials of 1.9.2, p. 42. Forgetting the redundant degree
    embeds the original finite prefix into a finite coordinate box. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds SymmetricCoordinateDualBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [finite_jet_degree_indices]: supporting finite
    coefficient index for Federer 3.4.8(5), p. 328: retain precisely
    the original degrees below l and their 1.9.2 monomials. *)
Definition finite_jet_degree_indices n l:finType:=
  Finite.clone {k:'I_l & symmetric_indices n (val k)} _.

(** Source for [finite_jet_degree_multiindex]: supporting original
    exponent tuple for the retained coefficient, Federer 3.4.8(5),
    p. 328, using the 1.9.2 index with its redundant bounds removed. *)
Definition finite_jet_degree_multiindex n l (j:finite_jet_degree_indices n l):=
  symmetric_indices_unbound (tagged j).

(** Source for [finite_jet_degree_multiindex_degree]: supporting
    exact original derivative degree, Federer 3.4.8(5), p. 328. *)
Lemma finite_jet_degree_multiindex_degree n l (j:finite_jet_degree_indices n l):
  symmetric_multi_degree (finite_jet_degree_multiindex j) = (tag j:nat).
Proof. exact:symmetric_indices_unbound_degree. Qed.

(** Source for [finite_jet_degree_multiindex_bound]: supporting
    coefficient count for Federer 3.4.8(5), p. 328: each original
    monomial exponent in a retained degree is smaller than l. *)
Lemma finite_jet_degree_multiindex_bound n l (j:finite_jet_degree_indices n l) i:
  finite_jet_degree_multiindex j i < l.
Proof.
have hh:=symmetric_multi_entry_bound (finite_jet_degree_multiindex j) i.
rewrite finite_jet_degree_multiindex_degree in hh.
exact:leq_ltn_trans hh (ltn_ord (tag j)).
Qed.

(** Source for [finite_jet_degree_box]: supporting injection into
    the l-by-...-by-l exponent box, Federer 3.4.8(5), p. 328.
    This map changes no actual derivative or factorial normalization. *)
Definition finite_jet_degree_box n l (j:finite_jet_degree_indices n l):
    {ffun 'I_n->'I_l}:=
  [ffun i=>Ordinal (finite_jet_degree_multiindex_bound j i)].

(** Source for [finite_jet_degree_box_injective]: supporting
    finite-jet dimension bound, Federer 3.4.8(5), p. 328.
    A retained original exponent tuple determines its degree and
    the original coefficient index, including empty source dimension. *)
Lemma finite_jet_degree_box_injective n l:injective (@finite_jet_degree_box n l).
Proof.
move=>[k a] [h b] hBoxes.
have hAB:symmetric_indices_unbound a = symmetric_indices_unbound b.
  apply/ffunP=>i.
  have hh:=congr1 (fun v:{ffun 'I_n->'I_l}=>val (v i)) hBoxes.
  rewrite /finite_jet_degree_box /= !ffunE /= !ffunE /= in hh.
  rewrite /finite_jet_degree_multiindex /= /symmetric_indices_unbound !ffunE in hh.
  rewrite /symmetric_indices_unbound !ffunE.
  exact hh.
have hKH:k = h.
  have hDegree:=congr1 (@symmetric_multi_degree n) hAB.
  rewrite !symmetric_indices_unbound_degree in hDegree.
  apply:val_inj;exact hDegree.
case:h /hKH b hBoxes hAB=>b hBoxes hAB.
congr (existT _ k _);exact:symmetric_indices_unbound_injective hAB.
Qed.

(** Source for [finite_jet_degree_card_upper]: supporting finite-jet
    growth bound for Federer 3.4.8(5), p. 328: there are at most
    l^n coefficients in degrees below l. Both zero endpoints remain. *)
Theorem finite_jet_degree_card_upper n l:#|finite_jet_degree_indices n l| <= l ^ n.
Proof.
have hh:=leq_card (@finite_jet_degree_box n l) (@finite_jet_degree_box_injective n l).
by rewrite card_ffun !card_ord in hh.
Qed.
