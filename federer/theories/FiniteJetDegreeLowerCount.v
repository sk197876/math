(** Supporting Federer (1969), 3.4.8(5), p. 328:
    count a box of original monomials inside a sufficiently long
    finite Taylor prefix. Use the exponent tuples of 1.9.2, p. 42. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds
  SymmetricCoordinateDualBasis FiniteJetDegreeIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [finite_jet_box_multiindex]: supporting original
    monomial exponents for Federer 3.4.8(5), p. 328, from the finite
    r-box without changing their values. *)
Definition finite_jet_box_multiindex n r (b:{ffun 'I_n->'I_r}):symmetric_multi_index n:=
  [ffun i=>val (b i)].

(** Source for [finite_jet_box_degree_bound]: supporting finite
    Taylor prefix for Federer 3.4.8(5), p. 328. Every original
    r-box monomial has degree at most n*r, including n=0. *)
Lemma finite_jet_box_degree_bound n r (b:{ffun 'I_n->'I_r}):
  symmetric_multi_degree (finite_jet_box_multiindex b) < (n*r).+1.
Proof.
rewrite ltnS /symmetric_multi_degree /finite_jet_box_multiindex.
have hh:(\sum_(i<n) val (b i)) <= \sum_(i<n) r.
  apply:leq_sum=>i _;exact:ltnW (ltn_ord (b i)).
rewrite sum_nat_const card_ord in hh.
under eq_bigr do rewrite ffunE.
exact:hh.
Qed.

(** Source for [finite_jet_box_degree_index]: supporting original
    exponent/degree connection for Federer 3.4.8(5), p. 328.
    Keep the actual exponent sum as the type's degree. *)
Definition finite_jet_box_degree_index n r (b:{ffun 'I_n->'I_r}):
    symmetric_degree_indices n (symmetric_multi_degree (finite_jet_box_multiindex b)):=
  @Sub (symmetric_multi_index n)
    (fun a=>symmetric_multi_degree a == symmetric_multi_degree (finite_jet_box_multiindex b))
    (symmetric_degree_indices n (symmetric_multi_degree (finite_jet_box_multiindex b)))
    (finite_jet_box_multiindex b) (eqxx (symmetric_multi_degree (finite_jet_box_multiindex b))).

(** Source for [finite_jet_box_to_degree_index]: supporting lower
    finite-jet count for Federer 3.4.8(5), p. 328. Include each
    original r-box monomial in its actual degree below n*r+1. *)
Definition finite_jet_box_to_degree_index n r (b:{ffun 'I_n->'I_r}):
    finite_jet_degree_indices n (n*r).+1:=
  existT (fun k:'I_(n*r).+1=>symmetric_indices n (val k))
    (Ordinal (finite_jet_box_degree_bound b))
    (symmetric_indices_bound (finite_jet_box_degree_index b)).

(** Source for [finite_jet_box_to_degree_index_injective]: supporting
    lower count for Federer 3.4.8(5), p. 328. Forgetting the selected
    degree recovers every original box coordinate. *)
Lemma finite_jet_box_to_degree_index_injective n r:
  injective (@finite_jet_box_to_degree_index n r).
Proof.
move=>b c hEqual.
have hh:=congr1 (@finite_jet_degree_multiindex n (n*r).+1) hEqual.
have hRecover (z:{ffun 'I_n->'I_r}):
    finite_jet_degree_multiindex (finite_jet_box_to_degree_index z) = finite_jet_box_multiindex z.
  change (val (symmetric_indices_forget
    (symmetric_indices_bound (finite_jet_box_degree_index z))) =
      finite_jet_box_multiindex z).
  by rewrite symmetric_indices_boundK.
rewrite !hRecover in hh.
apply/ffunP=>i;apply:val_inj.
have hCoordinate:=congr1 (fun a:symmetric_multi_index n=>a i) hh.
by move:hCoordinate;rewrite /finite_jet_box_multiindex !ffunE.
Qed.

(** Source for [finite_jet_degree_card_lower]: supporting original
    coefficient growth for Federer 3.4.8(5), p. 328: at least r^n
    monomials occur below degree n*r+1, also when n=0. *)
Theorem finite_jet_degree_card_lower n r:r ^ n <= #|finite_jet_degree_indices n (n*r).+1|.
Proof.
have hh:=leq_card (@finite_jet_box_to_degree_index n r)
  (@finite_jet_box_to_degree_index_injective n r).
by rewrite card_ffun !card_ord in hh.
Qed.
