(** Federer (1969), 1.10.5, p. 48: supporting finite-coordinate expression
    for the continuous product map used in the attainment argument.
    Algebraically this is distributivity in the symmetric algebra of 1.9.1,
    pp. 41-42. The supporting expansion below is not a separately numbered
    claim in these sources. It is valid over arbitrary fields. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finfun.
From Federer Require Import Bilinear SymmetricAlgebra SymmetricTupleScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Expansion.
Variable K : fieldType.
Variable V : lmodType K.
Local Notation E := (symmetric_space V).
Local Notation mu := (@symmetric_product K V).
Local Notation u := (symmetric_unit V).
Local Notation hb := (symmetric_product_bilinear V).
HB.instance Definition _ := Monoid.isLaw.Build E u mu
  (@symmetric_product_assoc K V) (@symmetric_product_unitl K V) (@symmetric_product_unitr K V).
HB.instance Definition _ := Monoid.isMulLaw.Build E (0:E) mu (bil0l hb) (bil0r hb).

(** Source for [symmetric_expansion_add]: Federer 1.10.5,
    p. 48, supporting additive operation for the finite distributive
    expansion of products. This is the existing vector addition. *)
Definition symmetric_expansion_add (x y : E) := x+y.
HB.instance Definition _ := Monoid.isComLaw.Build E (0:E) symmetric_expansion_add
  (@addrA E) (@addrC E) (@add0r E).
HB.instance Definition _ := Monoid.isAddLaw.Build E mu symmetric_expansion_add
  (bilDl hb) (bilDr hb).

(** Source for [symmetric_word_bigop]: Federer 1.10.5,
    p. 48, supporting identification of a word with the
    iterated algebra product of its generators, including the empty word. *)
Lemma symmetric_word_bigop (s : seq V) :
  symmetric_word s = \big[mu/u]_(v <- s) symmetric_generator v.
Proof. by elim: s=> [|v s ih]; rewrite ?big_nil ?big_cons ?symmetric_word_nil ?symmetric_word_cons ?ih. Qed.

(** Source for [symmetric_word_expansion]: Federer 1.10.5,
    p. 48, supporting coordinate expansion of the product map.
    Distributing a product of finite linear combinations gives the
    sum over all choices of one coordinate in each factor. *)
Theorem symmetric_word_expansion (I J : finType) (a : I -> J -> K) (e : J -> V) :
  symmetric_word [seq \sum_(j:J) a i j *: e j | i <- enum I] =
    \sum_(f : {ffun I -> J}) (\prod_(i:I) a i (f i)) *:
      symmetric_word [seq e (f i) | i <- enum I].
Proof.
have hen : index_enum I = enum I by rewrite /index_enum unlock enumT.
rewrite symmetric_word_bigop big_map -hen.
transitivity (\big[mu/u]_(i:I) \sum_(j:J) a i j *: symmetric_generator (e j)).
- apply: eq_bigr=> i _; rewrite linear_sum.
  apply: eq_bigr=> j _; exact: linearZ.
- have hd := @bigA_distr_bigA E (0:E) u
    (Monoid.MulLaw.clone E (0:E) mu _)
    (Monoid.AddLaw.clone E (0:E) mu symmetric_expansion_add _)
    I J (fun i j => a i j *: symmetric_generator (e j)).
  apply: eq_trans hd _; apply: eq_bigr=> f _.
  have hs := symmetric_word_scalars (fun i => e (f i)) (fun i => a i (f i)) (index_enum I).
  rewrite -hs symmetric_word_bigop big_map.
  apply: eq_bigr=> i _; symmetry; exact: linearZ.
Qed.
End Expansion.
