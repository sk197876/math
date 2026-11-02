(** Federer (1969), 1.9.4, p. 43: group the exponents beta<=alpha by their
    total degree p. These supporting finite bijections identify each degree
    fibre of the coordinate box with the corresponding bounded subset of
    Xi(n,p). *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices SymmetricIndexBounds SymmetricExponentBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_subindex]: Federer 1.9.4, p. 43,
    the displayed condition beta<=alpha on a degree-p index beta. *)
Definition symmetric_subindex n p (a : symmetric_multi_index n) (b : symmetric_indices n p) :=
  [forall i, symmetric_indices_unbound b i <= a i].

(** Source for [bounded_symmetric_indices]: Federer 1.9.4,
    p. 43, the finite subset of Xi(n,p) with beta<=alpha. *)
Definition bounded_symmetric_indices n (a : symmetric_multi_index n) p :=
  {b : symmetric_indices n p | symmetric_subindex a b}.

(** Source for [symmetric_box_degree_fibre]: Federer 1.9.4,
    p. 43, supporting restriction of the coordinate box to
    exponents whose total degree is p. *)
Definition symmetric_box_degree_fibre n (a : symmetric_multi_index n) p :=
  {c : symmetric_exponent_box a | symmetric_multi_degree (symmetric_exponent_box_index a c) == p}.

(** Source for [symmetric_box_fibre_index]: Federer 1.9.4,
    p. 43, the tuple from a degree-p box element, regarded
    as an index in Xi(n,p). *)
Definition symmetric_box_fibre_index n (a : symmetric_multi_index n) p
    (c : symmetric_box_degree_fibre a p) : symmetric_indices n p :=
  symmetric_indices_bound (Sub (symmetric_exponent_box_index a (val c)) (valP c)).

(** Source for [symmetric_box_fibre_indexE]: Federer 1.9.4,
    p. 43, forgetting bounds recovers the tuple represented by the box element. *)
Lemma symmetric_box_fibre_indexE n (a : symmetric_multi_index n) p (c : symmetric_box_degree_fibre a p) :
  symmetric_indices_unbound (symmetric_box_fibre_index c) = symmetric_exponent_box_index a (val c).
Proof.
have h := @symmetric_indices_boundK n p
  (Sub (symmetric_exponent_box_index a (val c)) (valP c)).
exact: (congr1 (fun z : symmetric_degree_indices n p => val z) h).
Qed.

(** Source for [symmetric_box_fibre_index_bound]: Federer
    1.9.4, p. 43, the degree-p index obtained from the box
    still satisfies the coordinate bound beta<=alpha. *)
Lemma symmetric_box_fibre_index_bound n (a : symmetric_multi_index n) p (c : symmetric_box_degree_fibre a p) :
  symmetric_subindex a (symmetric_box_fibre_index c).
Proof.
apply/forallP=> i; rewrite symmetric_box_fibre_indexE.
exact: symmetric_exponent_box_bound.
Qed.

(** Source for [symmetric_box_fibre_map]: Federer 1.9.4,
    p. 43, supporting map from the degree fibre to bounded Xi(n,p). *)
Definition symmetric_box_fibre_map n (a : symmetric_multi_index n) p
    (c : symmetric_box_degree_fibre a p) : bounded_symmetric_indices a p :=
  Sub (symmetric_box_fibre_index c) (symmetric_box_fibre_index_bound c).

(** Source for [symmetric_box_fibre_map_injective]: Federer
    1.9.4, p. 43, this map does not identify distinct box choices. *)
Lemma symmetric_box_fibre_map_injective n (a : symmetric_multi_index n) p :
  injective (@symmetric_box_fibre_map n a p).
Proof.
move=> x y h; apply: val_inj; apply: symmetric_exponent_box_injective.
have hh := congr1 (fun b : bounded_symmetric_indices a p => symmetric_indices_unbound (val b)) h.
by rewrite !symmetric_box_fibre_indexE in hh.
Qed.

(** Source for [symmetric_box_fibre_map_surjective]: Federer
    1.9.4, p. 43, every beta in Xi(n,p) with beta<=alpha
    occurs in the degree-p fibre. *)
Lemma symmetric_box_fibre_map_surjective n (a : symmetric_multi_index n) p
    (b : bounded_symmetric_indices a p) : exists c, symmetric_box_fibre_map c = b.
Proof.
have hb i : symmetric_indices_unbound (val b) i <= a i := forallP (valP b) i.
have [c hc] := symmetric_exponent_box_surjective hb.
have hd : symmetric_multi_degree (symmetric_exponent_box_index a c) == p.
  by rewrite hc symmetric_indices_unbound_degree.
exists (Sub c hd); apply: val_inj.
apply: (can_inj (@symmetric_indices_forgetK n p)); apply: val_inj.
change (symmetric_indices_unbound (symmetric_box_fibre_index (Sub c hd)) = symmetric_indices_unbound (val b)).
rewrite symmetric_box_fibre_indexE; exact: hc.
Qed.

(** Source for [symmetric_box_fibre_bijective]: Federer
    1.9.4, p. 43, the finite degree fibre is in bijection
    with exactly the inner summation indices in the book. *)
Lemma symmetric_box_fibre_bijective n (a : symmetric_multi_index n) p :
  bijective (@symmetric_box_fibre_map n a p).
Proof.
have hs b : b \in codom (@symmetric_box_fibre_map n a p).
  have [c hc] := symmetric_box_fibre_map_surjective b.
  apply/codomP; exists c; exact: esym hc.
exists (fun b => iinv (hs b)).
- move=> c; apply: (@symmetric_box_fibre_map_injective n a p).
  exact: f_iinv.
- move=> b; exact: f_iinv.
Qed.
