(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Federer 1.3.2: increasing sequences of basis indices. A recursive
    selection index records whether each basis vector is used. This is the
    indexing supplied by repeated direct sums with a one-dimensional space. *)
(** Source for [selection_index]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Fixpoint selection_index n : finType :=
  match n with
  | 0 => Finite.clone unit _
  | n'.+1 => Finite.clone (bool * selection_index n')%type _
  end.

(** Source for [selected_indices]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Fixpoint selected_indices n : selection_index n -> seq 'I_n :=
  match n as k return selection_index k -> seq 'I_k with
  | 0 => fun _ => [::]
  | n'.+1 => fun b =>
      let s := map (lift ord0) (@selected_indices n' b.2) in
      if b.1 then ord0 :: s else s
  end.
Arguments selected_indices n b : clear implicits.

(** Source for [selection_of]: Federer (1969), 1.3.2, p. 15, last sentence
    defining Lambda(n,m). In words: Lambda(n,m) is the set of strictly
    increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Fixpoint selection_of n : ('I_n -> bool) -> selection_index n :=
  match n as k return ('I_k -> bool) -> selection_index k with
  | 0 => fun _ => tt
  | n'.+1 => fun p => (p ord0, @selection_of n' (fun i => p (lift ord0 i)))
  end.
Arguments selection_of n p : clear implicits.

(** Source for [selected_size]: Federer (1969), 1.3.2, p. 15, last sentence
    defining Lambda(n,m). In words: Lambda(n,m) is the set of strictly
    increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_size n (b : selection_index n) : size (selected_indices n b) <= n.
Proof.
elim: n b => [b|n ih [b s]] //=.
by case: b; rewrite /= size_map; [exact: ih | exact: leq_trans (ih s) (leqnSn n)].
Qed.

(** Source for [selected_values]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_values n (b : bool) (s : selection_index n) :
  map val (selected_indices n.+1 (b,s)) =
  if b then 0 :: [seq (val i).+1 | i <- selected_indices n s]
  else [seq (val i).+1 | i <- selected_indices n s].
Proof. by case: b; rewrite /= -map_comp. Qed.

(** Source for [selected_sorted]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_sorted n (b : selection_index n) :
  sorted ltn (map val (selected_indices n b)).
Proof.
elim: n b => [b|n ih [b s]] //.
rewrite selected_values.
have hs : sorted ltn [seq (val i).+1 | i <- selected_indices n s].
  by rewrite map_comp sorted_map; exact: ih.
case: b => //.
move: hs; case: (selected_indices n s) => [|i t] //=.
Qed.

(** Source for [selected_mem_zero]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_mem_zero n (b : bool) (s : selection_index n) :
  (ord0 \in selected_indices n.+1 (b,s)) = b.
Proof.
have hn : ord0 \notin map (lift ord0) (selected_indices n s).
  apply/negP=> /mapP [i _ hi]; move: (neq_lift ord0 i).
  by rewrite -hi eqxx.
by case: b; rewrite /= ?inE ?eqxx (negbTE hn).
Qed.

(** Source for [selected_mem_lift]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_mem_lift n (b : bool) (s : selection_index n) (i : 'I_n) :
  (lift ord0 i \in selected_indices n.+1 (b,s)) = (i \in selected_indices n s).
Proof.
by case: b; rewrite /= ?inE ?lift_eqF ?orFb (mem_map (@lift_inj _ ord0)).
Qed.

(** Source for [selection_of_ext]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selection_of_ext n (p q : 'I_n -> bool) :
  (forall i, p i = q i) -> selection_of n p = selection_of n q.
Proof.
elim: n p q => [p q h|n ih p q h] //=.
by rewrite h; congr (_, _); apply: ih => i; exact: h.
Qed.

(** Source for [selection_ofK]: Federer (1969), 1.3.2, p. 15, last sentence
    defining Lambda(n,m). In words: Lambda(n,m) is the set of strictly
    increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selection_ofK n (b : selection_index n) :
  selection_of n (fun i => i \in selected_indices n b) = b.
Proof.
elim: n b => [[]|n ih [b s]] //=.
rewrite selected_mem_zero.
congr (_, _).
apply: eq_trans (_ : selection_of n (fun i => i \in selected_indices n s) = s); last exact: ih.
apply: selection_of_ext => i; exact: selected_mem_lift.
Qed.

(** Source for [selected_indices_injective]: Federer (1969), 1.3.2, p. 15,
    last sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_indices_injective n : injective (selected_indices n).
Proof.
move=> x y h; rewrite -(selection_ofK x) -(selection_ofK y).
by rewrite h.
Qed.

(** Source for [selected_mem_selection_of]: Federer (1969), 1.3.2, p. 15,
    last sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_mem_selection_of n (p : 'I_n -> bool) i :
  (i \in selected_indices n (selection_of n p)) = p i.
Proof.
elim: n p i => [p i|n ih p i]; first by have hz := valP i; rewrite ltn0 in hz.
case: (unliftP ord0 i) => [j ->|->]; rewrite /=.
- by rewrite selected_mem_lift ih.
- exact: selected_mem_zero.
Qed.

(** Federer's Lambda(n,m), with ordinal i representing his index i+1.
    The defining condition is precisely strict increase, and the count is
    the binomial coefficient from the final sentence of 1.3.2. *)
(** Source for [Lambda]: Federer (1969), 1.3.2, p. 15, last sentence
    defining Lambda(n,m). In words: Lambda(n,m) is the set of strictly
    increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Definition Lambda n m := {t : m.-tuple 'I_n | sorted ltn (map val t)}.
HB.instance Definition _ n m := Finite.copy (Lambda n m)
  {t : m.-tuple 'I_n | sorted ltn (map val t)}.

(** Source for [card_Lambda]: Federer (1969), 1.3.2, p. 15, last sentence
    defining Lambda(n,m). In words: Lambda(n,m) is the set of strictly
    increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Lemma card_Lambda n m : #|{: Lambda n m}| = 'C(n,m).
Proof.
rewrite card_sub -card_ltn_sorted_tuples.
by apply: eq_card => t; rewrite inE.
Qed.

(** Source for [selected_sequenceK]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selected_sequenceK n (s : seq 'I_n) :
  sorted ltn (map val s) ->
  selected_indices n (selection_of n (fun i => i \in s)) = s.
Proof.
move=> hs; apply: (inj_map val_inj).
apply: (irr_sorted_eq ltn_trans ltnn); first exact: selected_sorted.
- exact: hs.
- move=> k; apply/mapP/mapP => [[i hi ->]|[i hi ->]]; exists i => //.
  + by move: hi; rewrite selected_mem_selection_of.
  + by rewrite selected_mem_selection_of.
Qed.

(** Source for [degree_selection]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Definition degree_selection n m :=
  {b : selection_index n | size (selected_indices n b) == m}.
HB.instance Definition _ n m := Finite.copy (degree_selection n m)
  {b : selection_index n | size (selected_indices n b) == m}.

(** Source for [selection_tuple]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Definition selection_tuple n m (b : degree_selection n m) : m.-tuple 'I_n :=
  Tuple (valP b).
(** Source for [selection_Lambda]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Definition selection_Lambda n m (b : degree_selection n m) : Lambda n m :=
  Sub (selection_tuple b) (selected_sorted (val b)).

(** Source for [Lambda_selection_size]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_selection_size n m (t : Lambda n m) :
  size (selected_indices n (selection_of n (fun i => i \in val t))) == m.
Proof. by rewrite (selected_sequenceK (valP t)) size_tuple. Qed.
(** Source for [Lambda_selection]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Definition or construction used to
    formalise this passage. *)
Definition Lambda_selection n m (t : Lambda n m) : degree_selection n m :=
  Sub (selection_of n (fun i => i \in val t)) (Lambda_selection_size t).

(** Source for [selection_LambdaK]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selection_LambdaK n m :
  cancel (@selection_Lambda n m) (@Lambda_selection n m).
Proof. move=> b; apply: val_inj; exact: selection_ofK. Qed.
(** Source for [Lambda_selectionK]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_selectionK n m :
  cancel (@Lambda_selection n m) (@selection_Lambda n m).
Proof.
move=> t; apply: val_inj; apply: val_inj.
exact: selected_sequenceK (valP t).
Qed.

(** Source for [selection_LambdaE]: Federer (1969), 1.3.2, p. 15, last
    sentence defining Lambda(n,m). In words: Lambda(n,m) is the set of
    strictly increasing maps from the m indices to the n basis indices; its
    cardinality is binomial(n,m). Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma selection_LambdaE n m (t : Lambda n m) :
  selected_indices n (val (Lambda_selection t)) = val (val t).
Proof. exact: selected_sequenceK (valP t). Qed.
