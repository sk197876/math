(** Federer (1969), 1.10.1, pp. 43-44: symmetry under permutations of
    argument positions. This proves that the tuple rearrangement predicate
    matches the sources' explicit positional permutation formula. *)
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import SymmetricForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [tuple_symmetric_permutations]: Federer 1.10.1,
    pp. 43-44, opening displayed definition. Symmetry under sequence
    rearrangements is equivalent to invariance under every permutation
    of the m argument positions, including m=0. *)
Lemma tuple_symmetric_permutations (K : fieldType) (V W : lmodType K) m
    (f : m.-tuple V -> W) :
  tuple_symmetric f <->
    forall (t : m.-tuple V) (sigma : 'S_m),
      f [tuple tnth t (sigma i) | i < m] = f t.
Proof.
split.
- move=> hf t sigma; apply: hf.
  apply/tuple_permP; exists sigma; by [].
- move=> hf s t /tuple_permP [sigma hs].
  have he : s = [tuple tnth t (sigma i) | i < m] by apply: val_inj.
  by rewrite he hf.
Qed.

(** Source for [sform_permutation]: Federer 1.10.1, pp. 43-44,
    the opening displayed equation, applied to a symmetric form. *)
Lemma sform_permutation (K : fieldType) (V W : lmodType K) m
    (f : S_m V W m) (t : m.-tuple V) (sigma : 'S_m) :
  f [tuple tnth t (sigma i) | i < m] = f t.
Proof. exact: (proj1 (tuple_symmetric_permutations f) (sform_tuple_symmetric f)). Qed.
