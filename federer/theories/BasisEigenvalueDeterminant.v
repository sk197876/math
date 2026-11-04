(** Federer (1969), 3.2.46, p. 281: supporting positivity of
    det(L) from its positive eigenvalues. Expand the determinant
    formula of 1.3.4, p. 16, in any original eigenbasis; the
    implementation of the determinant remains sealed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals
  classical_sets fingroup perm.
From Federer Require Import TensorUP LinearBasis ExteriorDeterminant
  ExteriorLeibniz PermutationDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [basis_eigenvalue_determinant]: the determinant
    of a map diagonal in an arbitrary given basis is the product
    of its eigenvalues, by Federer 1.3.4, p. 16; supporting
    det(L)>0 in 3.2.46, p. 281. Empty bases give determinant one. *)
Lemma basis_eigenvalue_determinant (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) n (e : 'I_n -> V) (he : is_basis e)
    (L : {linear V -> V}) (c : 'I_n -> K) :
  (forall i, L (e i) = c i *: e i) ->
  det h2 he L = \prod_(i < n) c i.
Proof.
move=> hL.
rewrite (det_formula h2 he (f := L)
  (b := fun i j => if i == j then c i else 0)); last first.
  move=> i; rewrite hL (bigD1 i) //= eqxx.
  rewrite big1 ?addr0 // => j hji.
  by rewrite eq_sym (negbTE hji) scale0r.
rewrite (bigD1 (1%g : 'S_n)) //= index_one ?h2 // mul1r.
rewrite [X in _+X]big1 ?addr0; first by apply: eq_bigr=> i _; rewrite perm1 eqxx.
move=> s hs; case: (pselect (exists i, s i != i))=> [[i hi]|hne].
- by rewrite (bigD1 i) //= eq_sym (negbTE hi) mul0r mulr0.
- exfalso; move: hs=> /eqP; apply; apply/permP=> i; rewrite perm1.
  by apply/eqP; apply: contrapT=> h; apply: hne; exists i; exact/negP.
Qed.

(** Source for [positive_basis_eigenvalue_determinant]: the
    positive determinant of the local frozen map in Federer
    3.2.46, p. 281, follows from its strictly positive eigenvalues.
    This supporting statement also includes an empty eigenbasis. *)
Lemma positive_basis_eigenvalue_determinant (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R) n
    (e : 'I_n -> V) (he : is_basis e) (L : {linear V -> V})
    (c : 'I_n -> R) :
  (forall i, 0 < c i) -> (forall i, L (e i) = c i *: e i) ->
  0 < det h2 he L.
Proof.
move=> hc hL; rewrite (@basis_eigenvalue_determinant R h2 V n e he L c hL).
apply: prodr_gt0=> i _; exact: hc.
Qed.
