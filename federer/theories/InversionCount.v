(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import Shuffles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.

(** Federer 1.3.3: N counts pairs (i,j) with i<j and sigma(i)>sigma(j).
    This enumeration contains precisely those pairs, without repetition. *)
(** Source for [inversion_pairs]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Definition or construction
    used to formalise this passage. *)
Fixpoint inversion_pairs (s : seq nat) : seq (nat * nat) :=
  if s is x :: t then
    [seq (0,j.+1) | j <- iota 0 (size t) & nth 0 t j < x] ++
    [seq (ij.1.+1,ij.2.+1) | ij <- inversion_pairs t]
  else [::].

(** Source for [inversion_pairs_spec]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma inversion_pairs_spec s i j :
  ((i,j) \in inversion_pairs s) = [&& i < j, j < size s & nth 0 s j < nth 0 s i].
Proof.
elim: s => [|x s ih] in i j *.
- by rewrite /= in_nil andbF.
rewrite /= mem_cat; apply/idP/idP.
- move/orP=> [/mapP [k hk he]|/mapP [[a b] hab he]].
  + case: he => -> ->; move: hk; rewrite mem_filter mem_iota add0n leq0n /=.
    by move/andP=> [hx hk]; rewrite ?ltnS hk hx.
  + case: he => -> ->; by rewrite /= ?ltnS -ih.
- case: i => [|i]; case: j => [|j] /=; rewrite ?ltn0 ?andbF //.
  + rewrite ?ltn0Sn /= ?ltnS => /andP [hj hx].
    apply/orP; left; apply/mapP; exists j => //.
    by rewrite mem_filter mem_iota add0n leq0n hj hx.
  + rewrite !ltnS => h; apply/orP; right; apply/mapP; exists (i,j) => //.
    by rewrite ih.
Qed.

(** Source for [inversion_row_injective]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversion_row_injective : injective (fun j : nat => (0,j.+1)).
Proof. move=> i j h; apply: succn_inj; exact (congr1 snd h). Qed.
(** Source for [inversion_shift_injective]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversion_shift_injective : injective (fun ij : nat * nat => (ij.1.+1,ij.2.+1)).
Proof.
move=> [i j] [k l] h.
have hi : i = k := succn_inj (congr1 fst h).
have hj : j = l := succn_inj (congr1 snd h).
by rewrite hi hj.
Qed.
(** Source for [inversion_pairs_uniq]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma inversion_pairs_uniq s : uniq (inversion_pairs s).
Proof.
elim: s => [|x s ih] //=.
rewrite cat_uniq (map_inj_uniq inversion_row_injective)
  (map_inj_uniq inversion_shift_injective) ih andbT.
apply/andP; split; first exact: filter_uniq (iota_uniq 0 (size s)).
apply/hasPn=> ij /mapP [[i j] hij ->]; apply/negP=> /mapP [k hk he].
by have h := congr1 fst he; discriminate h.
Qed.

(** Source for [count_initial_indices]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma count_initial_indices s x :
  count (fun j => nth 0 s j < x) (iota 0 (size s)) = count (fun y => y < x) s.
Proof.
have hm : [seq nth 0 s j | j <- iota 0 (size s)] = s.
  by rewrite map_nth_iota0 // take_size.
have h := congr1 (count (fun y => y < x)) hm.
by rewrite count_map in h.
Qed.
(** Source for [inversions_pair_count]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversions_pair_count s : inversions s = size (inversion_pairs s).
Proof.
elim: s => [|x s ih] //=.
by rewrite size_cat !size_map size_filter count_initial_indices ih.
Qed.

(** Source for [inversion_set]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Definition or construction
    used to formalise this passage. *)
Definition inversion_set n (s : 'S_n) : {set ('I_n * 'I_n)%type} :=
  [set ij : ('I_n * 'I_n)%type | (ij.1 < ij.2) && (s ij.2 < s ij.1)].
(** Source for [ordinal_pair_values]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Definition or construction
    used to formalise this passage. *)
Definition ordinal_pair_values n (ij : ('I_n * 'I_n)%type) : nat * nat :=
  (val ij.1, val ij.2).
(** Source for [ordinal_pair_values_injective]: Federer (1969), 1.3.3, p.
    15, sentence immediately after the shuffle formula. In words: The index
    of a permutation is (-1) raised to its number of inversions, namely
    pairs i<j whose images occur in the opposite order. Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma ordinal_pair_values_injective n : injective (@ordinal_pair_values n).
Proof.
move=> [i j] [k l] h.
have hi : i = k := val_inj (congr1 fst h).
have hj : j = l := val_inj (congr1 snd h).
by rewrite hi hj.
Qed.
(** Source for [permutation_values_nth]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma permutation_values_nth n (s : 'S_n) (i : 'I_n) :
  nth 0 (map val (permutation_sequence s)) (val i) = val (s i).
Proof.
have h := tnth_nth 0 [tuple of map val (permutation_sequence s)] i.
by rewrite tnth_map tnth_mktuple in h.
Qed.
(** Source for [inversion_pair_enum_mem]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma inversion_pair_enum_mem n (s : 'S_n) i j :
  ((i,j) \in map (@ordinal_pair_values n) (enum (inversion_set s))) =
  ((i,j) \in inversion_pairs (map val (permutation_sequence s))).
Proof.
rewrite inversion_pairs_spec size_map size_tuple.
apply/idP/idP.
- move/mapP=> [[a b] hab he]; case: he => -> ->.
  rewrite !permutation_values_nth; move: hab; rewrite mem_enum inE => /andP [hab hba].
  by rewrite hab (valP b) hba.
- move/and3P=> [hij hj hji].
  pose a : 'I_n := Ordinal (ltn_trans hij hj).
  pose b : 'I_n := Ordinal hj.
  apply/mapP; exists (a,b) => //.
  rewrite mem_enum inE; apply/andP; split; first exact: hij.
  change (is_true (nth 0 (map val (permutation_sequence s)) (val b) <
    nth 0 (map val (permutation_sequence s)) (val a))) in hji.
  by rewrite !permutation_values_nth in hji.
Qed.
(** Source for [inversions_permutation_card]: Federer (1969), 1.3.3, p. 15,
    sentence immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Formalises the indicated part
    of the passage under the hypotheses in the statement below. *)
Lemma inversions_permutation_card n (s : 'S_n) :
  inversions (map val (permutation_sequence s)) = #|inversion_set s|.
Proof.
have hp : perm_eq (map (@ordinal_pair_values n) (enum (inversion_set s)))
    (inversion_pairs (map val (permutation_sequence s))).
  apply: uniq_perm.
  - by rewrite (map_inj_uniq (@ordinal_pair_values_injective n)) enum_uniq.
  - exact: inversion_pairs_uniq.
  - by case=> i j; exact: inversion_pair_enum_mem.
have h := perm_size hp.
by rewrite size_map -cardE -inversions_pair_count in h.
Qed.

Module FedererPermutation.
Local Open Scope ring_scope.
(** Source for [index]: Federer (1969), 1.3.3, p. 15, sentence immediately
    after the shuffle formula. In words: The index of a permutation is (-1)
    raised to its number of inversions, namely pairs i<j whose images occur
    in the opposite order. Definition or construction used to formalise this
    passage. *)
Definition index (K : fieldType) n (s : 'S_n) : K :=
  (-1 : K)^+(inversions (map val (permutation_sequence s))).
(** Source for [index_pairs]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma index_pairs (K : fieldType) n (s : 'S_n) :
  index K s = (-1 : K)^+(size (inversion_pairs (map val (permutation_sequence s)))).
Proof. by rewrite /index inversions_pair_count. Qed.
(** Source for [index_inversions]: Federer (1969), 1.3.3, p. 15, sentence
    immediately after the shuffle formula. In words: The index of a
    permutation is (-1) raised to its number of inversions, namely pairs i<j
    whose images occur in the opposite order. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem index_inversions (K : fieldType) n (s : 'S_n) :
  index K s = (-1 : K)^+(#|[set ij : ('I_n * 'I_n)%type |
    (ij.1 < ij.2)%N && (s ij.2 < s ij.1)%N]|).
Proof. by rewrite /index inversions_permutation_card. Qed.
End FedererPermutation.
