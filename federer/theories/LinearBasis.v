(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From mathcomp.classical Require Import boolp.
From Federer Require Import TensorUP FreeVector Bilinear GradedAlgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.2 and 1.3.2: bases in arbitrary dimension. The coefficient
    space consists of finitely supported functions; synthesis is the finite
    linear combination. The predicate asks for inverse linear coordinates. *)
Section Basis.
Variable K : fieldType.
Variable I : choiceType.
Variable V : lmodType K.
Variable e : I -> V.
Local Notation F := (GRing.Lmodule.clone K (free_vector K I) _).

(** Source for [basis_synthesis]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Definition or construction used to formalise this
    passage. *)
Definition basis_synthesis : {linear F -> V} :=
  GRing.Linear.clone _ _ _ _ (free_extend e) _.
(** Source for [is_basis]: Federer (1969), 1.1.2, p. 10, final paragraph and
    dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Definition or construction used to formalise this passage. *)
Definition is_basis : Prop := exists c : {linear V -> F},
  cancel basis_synthesis c /\ cancel c basis_synthesis.

(** Source for [basis_synthesisE]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_synthesisE i : basis_synthesis (delta K i) = e i.
Proof. exact: free_extend_delta. Qed.

Variable hb : is_basis.
(** Source for [basis_coordinates]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Definition or construction used to formalise this
    passage. *)
Definition basis_coordinates : {linear V -> F} :=
  sval (constructive_indefinite_description hb).
(** Source for [basis_synthesisK]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_synthesisK : cancel basis_synthesis basis_coordinates.
Proof. exact: (proj1 (svalP (constructive_indefinite_description hb))). Qed.
(** Source for [basis_coordinatesK]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_coordinatesK : cancel basis_coordinates basis_synthesis.
Proof. exact: (proj2 (svalP (constructive_indefinite_description hb))). Qed.
(** Source for [basis_coordinatesE]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_coordinatesE i : basis_coordinates (e i) = delta K i.
Proof. by rewrite -basis_synthesisE basis_synthesisK. Qed.
(** Source for [basis_synthesis_injective]: Federer (1969), 1.1.2, p. 10,
    final paragraph and dimension formula. In words: Pure tensors formed
    from bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_synthesis_injective : injective basis_synthesis.
Proof. exact: can_inj basis_synthesisK. Qed.

(** Source for [basis_induction]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_induction (P : V -> Prop) (h0 : P 0)
    (hD : forall x y, P x -> P y -> P (x + y))
    (hZ : forall a x, P x -> P (a *: x))
    (he : forall i, P (e i)) : forall x, P x.
Proof.
move=> x; rewrite -[x]basis_coordinatesK.
elim/free_induction: (basis_coordinates x) => [|u v hu hv|a u hu|i].
- by rewrite linear0.
- rewrite linearD; exact: hD hu hv.
- rewrite linearZ; exact: hZ hu.
by rewrite basis_synthesisE.
Qed.

(** Source for [basis_linear_ext]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_linear_ext (W : lmodType K) (f g : {linear V -> W}) :
  (forall i, f (e i) = g (e i)) -> forall x, f x = g x.
Proof.
move=> he; apply: basis_induction => [|x y hx hy|a x hx|i].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
exact: he.
Qed.
End Basis.
Arguments basis_linear_ext {K I V e} hb {W} f g _ x.

(** Source for [basis_congr]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma basis_congr (K : fieldType) (I : choiceType) (V : lmodType K)
    (e d : I -> V) : (forall i, e i = d i) -> is_basis e -> is_basis d.
Proof.
move=> he [c [hc hd]].
have hs : forall x, basis_synthesis d x = basis_synthesis e x.
  apply: (free_linear_ext (basis_synthesis d) (basis_synthesis e)) => i.
  by rewrite !basis_synthesisE he.
exists c; split=> x; first by rewrite hs hc.
by rewrite hs hd.
Qed.

Section Inverse.
Variable K : fieldType.
Variables V W : lmodType K.
Variable f : {linear V -> W}.
Hypothesis hinj : injective f.
Hypothesis hsurj : forall w, exists v, f v = w.
(** Source for [linear_inverse]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Definition or construction used to formalise this
    passage. *)
Definition linear_inverse (w : W) : V := let _ := hinj in sval (constructive_indefinite_description (hsurj w)).
(** Source for [linear_inverseK]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma linear_inverseK : cancel linear_inverse f.
Proof. move=> w; exact: (svalP (constructive_indefinite_description (hsurj w))). Qed.
(** Source for [linear_inverseKV]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma linear_inverseKV : cancel f linear_inverse.
Proof. by move=> v; apply: hinj; rewrite linear_inverseK. Qed.
(** Source for [linear_inverse_linear]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma linear_inverse_linear : linear linear_inverse.
Proof. by move=> a x y; apply: hinj; rewrite linearP !linear_inverseK. Qed.
HB.instance Definition _ := GRing.isLinear.Build K W V *:%R linear_inverse linear_inverse_linear.
End Inverse.

(** The basis predicate is equivalent to uniqueness and existence of finite
    linear combinations: linear independence together with spanning. *)
(** Source for [basisP]: Federer (1969), 1.1.2, p. 10, final paragraph and
    dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Lemma basisP (K : fieldType) (I : choiceType) (V : lmodType K) (e : I -> V) :
  is_basis e <-> injective (basis_synthesis e) /\
    (forall v, exists c, basis_synthesis e c = v).
Proof.
split.
- move=> hb; split; first exact: basis_synthesis_injective hb.
  by move=> v; exists (basis_coordinates hb v); exact: basis_coordinatesK.
- move=> [hi hs]; exists (GRing.Linear.clone _ _ _ _ (linear_inverse hi hs) _).
  split; [exact: linear_inverseKV | exact: linear_inverseK].
Qed.

Section FreeBasis.
Variable K : fieldType.
Variable I : choiceType.
Local Notation F := (GRing.Lmodule.clone K (free_vector K I) _).
(** Source for [free_synthesis_id]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma free_synthesis_id (x : F) : basis_synthesis (@delta K I) x = x.
Proof. exact: esym (free_expansion x). Qed.
(** Source for [free_basis]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma free_basis : is_basis (@delta K I).
Proof. exists (linear_id F); split; exact: free_synthesis_id. Qed.
End FreeBasis.

Section Transport.
Variable K : fieldType.
Variable I : choiceType.
Variables V W : lmodType K.
Variable e : I -> V.
Variable f : {linear V -> W}.

(** Source for [basis_synthesis_comp]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_synthesis_comp x : basis_synthesis (fun i => f (e i)) x = f (basis_synthesis e x).
Proof.
elim/free_induction: x => [|x y hx hy|a x hx|i].
- by rewrite !linear0.
- by rewrite !linearD hx hy.
- by rewrite !linearZ hx.
by rewrite !basis_synthesisE.
Qed.

Variable g : {linear W -> V}.
Hypotheses (fg : cancel f g) (gf : cancel g f).
(** Source for [basis_transport]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_transport : is_basis e -> is_basis (fun i => f (e i)).
Proof.
move=> hb; exists (linear_comp (basis_coordinates hb) g); split=> x.
- change (basis_coordinates hb (g (basis_synthesis (fun i => f (e i)) x)) = x).
  by rewrite basis_synthesis_comp fg basis_synthesisK.
- change (basis_synthesis (fun i => f (e i)) (basis_coordinates hb (g x)) = x).
  by rewrite basis_synthesis_comp basis_coordinatesK gf.
Qed.
End Transport.

Section Reindex.
Variable K : fieldType.
Variables I J : choiceType.
Variable h : I -> J.
(** Source for [free_map]: Federer (1969), 1.1.2, p. 10, final paragraph and
    dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Definition or construction used to formalise this passage. *)
Definition free_map : {linear free_vector K I -> free_vector K J} :=
  GRing.Linear.clone _ _ _ _ (free_extend (fun i => delta K (h i))) _.
(** Source for [free_mapE]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma free_mapE i : free_map (delta K i) = delta K (h i).
Proof. exact: free_extend_delta. Qed.
End Reindex.

Section ReindexInverse.
Variable K : fieldType.
Variables I J : choiceType.
Variables (h : I -> J) (k : J -> I).
Hypothesis hk : cancel h k.
(** Source for [free_mapK]: Federer (1969), 1.1.2, p. 10, final paragraph
    and dimension formula. In words: Pure tensors formed from bases of the
    factors form a basis of the tensor product; finite dimensions multiply.
    Supporting lemma for this passage; not separately stated in the book. *)
Lemma free_mapK : cancel (free_map K h) (free_map K k).
Proof.
apply: (free_linear_ext (linear_comp (free_map K k) (free_map K h))
  (linear_id (GRing.Lmodule.clone K (free_vector K I) _))) => i.
change (free_map K k (free_map K h (delta K i)) = delta K i).
by rewrite !free_mapE hk.
Qed.
End ReindexInverse.

Section BasisReindex.
Variable K : fieldType.
Variables I J : choiceType.
Variable V : lmodType K.
Variable e : I -> V.
Variable hb : is_basis e.
Variables (h : I -> J) (k : J -> I).
Hypotheses (hk : cancel h k) (kh : cancel k h).
Local Notation FJ := (GRing.Lmodule.clone K (free_vector K J) _).

(** Source for [basis_reindex]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma basis_reindex : is_basis (fun j => e (k j)).
Proof.
exists (linear_comp (free_map K h) (basis_coordinates hb)); split.
- apply: (free_linear_ext
    (linear_comp (linear_comp (free_map K h) (basis_coordinates hb))
      (basis_synthesis (fun j => e (k j)))) (linear_id FJ)) => j.
  change (free_map K h (basis_coordinates hb
    (basis_synthesis (fun j => e (k j)) (delta K j))) = delta K j).
  by rewrite basis_synthesisE basis_coordinatesE free_mapE kh.
- apply: (basis_linear_ext hb
    (linear_comp (basis_synthesis (fun j => e (k j)))
      (linear_comp (free_map K h) (basis_coordinates hb))) (linear_id V)) => i.
  change (basis_synthesis (fun j => e (k j))
    (free_map K h (basis_coordinates hb (e i))) = e i).
  by rewrite basis_coordinatesE free_mapE basis_synthesisE hk.
Qed.
End BasisReindex.

(** Federer 1.3.2 also uses the degrees of basis elements in its direct sums. *)
(** Source for [is_graded_basis]: Federer (1969), 1.1.2, p. 10, final
    paragraph and dimension formula. In words: Pure tensors formed from
    bases of the factors form a basis of the tensor product; finite
    dimensions multiply. Definition or construction used to formalise this
    passage. *)
Definition is_graded_basis (K : fieldType) (I : choiceType) (V : lmodType K)
    (G : grading V) (e : I -> V) (d : I -> nat) :=
  is_basis e /\ forall i, homogeneous G (d i) (e i).
