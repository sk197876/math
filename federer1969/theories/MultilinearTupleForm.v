(** Federer (1969), 3.1.11, pp. 219–220:
    identification of the finite-family multilinear
    interface with the tuple-based forms of
    1.4.1, pp. 16–17, and 1.10.1,
    pp. 43–44. *)
From mathcomp Require Import all_boot all_order all_algebra boolp fingroup perm.
From Federer Require Import TensorFamilyUP PowerWords WordEvaluation
  AlternatingForms SymmetricForms SymmetricFormPermutations FiniteArgumentPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [multilinear_word_tuple_value]:
    on an m-tuple the word extension is
    the original m-linear value, supporting
    Federer 3.1.11, p. 220, and
    the form conventions of 1.10.1, p. 43. *)
Lemma multilinear_word_tuple_value (K : fieldType)
    (X Y : lmodType K) m (F : {ffun 'I_m->X}->Y) (t : m.-tuple X) :
  beta_words F t=F [ffun i=>tnth t i].
Proof.
rewrite /beta_words size_tuple eqxx; congr (F _).
by apply/ffunP=>i; rewrite /seq_to_power !ffunE (tnth_nth 0).
Qed.

(** Source for [multilinear_family_tuple_linear]:
    the two formulations of multilinearity agree:
    replacing one finite-family entry or one
    prefix/suffix tuple entry is the same operation.
    This supports Federer 3.1.11, p. 220,
    with the conventions of 1.4.1, pp. 16–17. *)
Lemma multilinear_family_tuple_linear (K : fieldType)
    (X Y : lmodType K) m (F : {ffun 'I_m->X}->Y) :
  multilinear F -> m_linear (fun t : m.-tuple X=>F [ffun i=>tnth t i]).
Proof.
move=> hF s t h c x y.
have hh := beta_words_multilinear hF s t c x y.
have ht v : beta_words F (s++v::t)=
    F [ffun i=>tnth (context_tuple s t h v) i].
  exact: multilinear_word_tuple_value F (context_tuple s t h v).
by rewrite -!ht.
Qed.

(** Source for [multilinear_family_tuple_symmetric]:
    permutation symmetry of the finite-family
    evaluation is exactly tuple symmetry, supporting
    Federer 3.1.11, p. 220, and
    1.10.1, pp. 43–44. *)
Lemma multilinear_family_tuple_symmetric (K : fieldType)
    (X Y : lmodType K) m (F : {ffun 'I_m->X}->Y) :
  (forall s u, F (finite_argument_permutation s u)=F u) ->
  tuple_symmetric (fun t : m.-tuple X=>F [ffun i=>tnth t i]).
Proof.
move=> hF; apply: (tuple_symmetric_permutations _).2=>t s.
have he : [ffun i=>tnth [tuple tnth t (s j) | j<m] i]=
    finite_argument_permutation s [ffun i=>tnth t i].
  by apply/ffunP=>i; rewrite /finite_argument_permutation !ffunE tnth_mktuple.
by rewrite he hF.
Qed.

(** Source for [symmetric_multilinear_tuple_form_exists]:
    a symmetric multilinear finite-family evaluation
    determines a symmetric form of the project's
    Chapter 1 interface, as asserted for higher
    differentials in Federer 3.1.11, p. 220. *)
Theorem symmetric_multilinear_tuple_form_exists (K : fieldType)
    (X Y : lmodType K) m (F : {ffun 'I_m->X}->Y) :
  multilinear F ->
  (forall s u, F (finite_argument_permutation s u)=F u) ->
  exists phi : S_m X Y m, forall t, phi t=F [ffun i=>tnth t i].
Proof.
move=> hlin hsym.
have hp : sform_pred (fun t : m.-tuple X=>F [ffun i=>tnth t i]).
  apply/asboolP; split.
  - exact: multilinear_family_tuple_linear hlin.
  - exact: multilinear_family_tuple_symmetric hsym.
by exists (@SymmetricForm K X Y m _ hp).
Qed.
