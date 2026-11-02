(** Federer (1969), 1.9.4, p. 43: the condition beta<=alpha in the monomial
    diagonal formula. A recursive finite product of the coordinate ranges
    enumerates these beta exactly once. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import SymmetricMultiIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [symmetric_multi_difference]: Federer 1.9.4,
    p. 43, the coordinatewise difference alpha-beta. It is
    used under beta<=alpha in the displayed diagonal formula. *)
Definition symmetric_multi_difference n (a b : symmetric_multi_index n) : symmetric_multi_index n :=
  [ffun i => a i - b i].

(** Source for [symmetric_multi_difference_cons]: Federer
    1.9.4, p. 43, supporting decomposition of coordinatewise
    subtraction into the first entry and the tail. *)
Lemma symmetric_multi_difference_cons n k l (a b : symmetric_multi_index n) :
  symmetric_multi_difference (symmetric_multi_cons k a) (symmetric_multi_cons l b) =
    symmetric_multi_cons (k-l) (symmetric_multi_difference a b).
Proof.
apply/ffunP=> i; rewrite /symmetric_multi_difference /symmetric_multi_cons !ffunE.
by case: (unlift ord0 i)=> [j|] //; rewrite ffunE.
Qed.

(** Source for [symmetric_exponent_box]: Federer 1.9.4,
    p. 43, supporting finite product of coordinate ranges
    0,...,alpha_i, used to enumerate all beta<=alpha. *)
Fixpoint symmetric_exponent_box n : symmetric_multi_index n -> finType :=
  match n as k return symmetric_multi_index k -> finType with
  | 0 => fun _ => Finite.clone unit _
  | k.+1 => fun a => Finite.clone
      ('I_(symmetric_multi_head a).+1 * @symmetric_exponent_box k (symmetric_multi_tail a))%type _
  end.

(** Source for [symmetric_exponent_box_index]: Federer 1.9.4,
    p. 43, reconstruct the exponent tuple beta from its finite
    coordinate choices. *)
Fixpoint symmetric_exponent_box_index n : forall a : symmetric_multi_index n,
    symmetric_exponent_box a -> symmetric_multi_index n :=
  match n as k return forall a : symmetric_multi_index k,
      symmetric_exponent_box a -> symmetric_multi_index k with
  | 0 => fun _ _ => symmetric_multi_zero 0
  | k.+1 => fun a b => symmetric_multi_cons (val b.1)
      (@symmetric_exponent_box_index k (symmetric_multi_tail a) b.2)
  end.

Arguments symmetric_exponent_box_index {n} a b.

(** Source for [symmetric_exponent_box_bound]: Federer 1.9.4,
    p. 43, every reconstructed exponent satisfies beta_i<=alpha_i. *)
Lemma symmetric_exponent_box_bound n (a : symmetric_multi_index n) (b : symmetric_exponent_box a) i :
  symmetric_exponent_box_index a b i <= a i.
Proof.
elim: n a b i=> [a b i|n ih a [k b] i].
- by case: i=> i.
- rewrite /= /symmetric_multi_cons ffunE.
  case: (unliftP ord0 i)=> [j ->|->].
  + have h := ih (symmetric_multi_tail a) b j.
    by rewrite /symmetric_multi_tail ffunE in h.
  + exact: (valP k).
Qed.

(** Source for [symmetric_exponent_box_injective]: Federer
    1.9.4, p. 43, the coordinate enumeration has no repetitions. *)
Lemma symmetric_exponent_box_injective n (a : symmetric_multi_index n) :
  injective (symmetric_exponent_box_index a).
Proof.
elim: n a=> [a [] [] _|n ih a [k b] [l c] h] //.
have hkl : k = l.
  apply: val_inj; have hh := congr1 (@symmetric_multi_head n) h.
  by rewrite !symmetric_multi_cons_head in hh.
congr (_, _); first exact: hkl.
apply: ih; have ht := congr1 (@symmetric_multi_tail n) h.
by rewrite !symmetric_multi_cons_tail in ht.
Qed.

(** Source for [symmetric_exponent_box_surjective]: Federer
    1.9.4, p. 43, every exponent tuple beta<=alpha is
    represented by the finite coordinate enumeration. *)
Lemma symmetric_exponent_box_surjective n (a b : symmetric_multi_index n) :
  (forall i, b i <= a i) ->
  exists c : symmetric_exponent_box a, symmetric_exponent_box_index a c = b.
Proof.
elim: n a b=> [a b hb|n ih a b hb].
- exists tt; exact: esym (symmetric_multi_index_empty b).
- have ht : forall i, symmetric_multi_tail b i <= symmetric_multi_tail a i.
    by move=> i; rewrite /symmetric_multi_tail !ffunE; exact: hb.
  have [c hc] := ih _ _ ht.
  have hk : symmetric_multi_head b < (symmetric_multi_head a).+1 := hb ord0.
  exists (Ordinal hk,c); rewrite /= hc; exact: symmetric_multi_head_tail.
Qed.

(** Source for [symmetric_exponent_box_degree_bound]: Federer
    1.9.4, p. 43, grouping the box by degree only needs
    degrees p between zero and the total degree of alpha. *)
Lemma symmetric_exponent_box_degree_bound n (a : symmetric_multi_index n) (b : symmetric_exponent_box a) :
  symmetric_multi_degree (symmetric_exponent_box_index a b) <= symmetric_multi_degree a.
Proof.
apply: leq_sum=> i _; exact: symmetric_exponent_box_bound.
Qed.
