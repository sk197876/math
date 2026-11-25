(** Federer (1969), 3.1.24, pp. 239–240: scalar
    symmetric forms are determined by their value on unit
    arguments. This supports the inverse-majorant coefficient
    calculation through the exact higher-composition formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom TensorFamilyUP MultilinearFamilyAlgebra BoundedHom
  SymmetricAlgebra SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricFormWords ContinuousSymmetricFormAdapter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_symmetric_form_evaluation]: the scalar
    forms in Federer's composition and inverse calculations,
    3.1.24, pp. 239–240, evaluate as the product of
    their arguments times their coefficient at the tuple of
    ones. This algebraic identity also holds in degree zero. *)
Lemma scalar_symmetric_form_evaluation (K:fieldType) m (Y:lmodType K)
    (phi:S_m K^o Y m) (t:m.-tuple K^o) :
  phi t=(\prod_(i<m) tnth t i)*:phi [tuple (1:K^o) | i<m].
Proof.
pose ones:{ffun 'I_m->K^o}:=[ffun i=>(1:K^o)].
pose u:{ffun 'I_m->K^o}:=[ffun i=>tnth t i].
have hh:=@multilinear_family_scale_all K m (fun _=>[the lmodType K of K^o]) Y
  (fun w:{ffun 'I_m->K^o}=>phi [tuple w i | i<m]) (sform_finite_family_multilinear phi) ones u.
have ht:[tuple [ffun i:'I_m=>u i*:ones i] j | j<m]= t.
  apply:eq_from_tnth=>i; rewrite tnth_mktuple ffunE /ones !ffunE.
  change (tnth t i*1=tnth t i); exact: mulr1.
rewrite ht in hh.
have hOne:[tuple ones i | i<m]= [tuple (1:K^o) | i<m].
  apply:eq_from_tnth=>i; by rewrite !tnth_mktuple /ones ffunE.
have hProd:(\prod_(i<m) u i)=\prod_(i<m) tnth t i.
  by apply:eq_bigr=>i _; rewrite /u ffunE.
by rewrite hOne hProd in hh.
Qed.

(** Source for [scalar_symmetric_form_word_evaluation]: the
    scalar symmetric word evaluation needed for the normalized
    composition coefficient sum in Federer 3.1.24, pp. 239–240.
    The word has exactly the form's degree. *)
Lemma scalar_symmetric_form_word_evaluation (K:fieldType) m (Y:lmodType K)
    (phi:S_m K^o Y m) (s:seq K^o) :
  size s=m -> sform_homogeneous phi (symmetric_word s)=
    (\prod_(x<-s) x)*:phi [tuple (1:K^o) | i<m].
Proof.
move=>hs.
pose t:m.-tuple K^o:=Tuple (introT eqP hs).
change (sform_homogeneous phi (symmetric_word t)=
  (\prod_(x<-t) x)*:phi [tuple (1:K^o) | i<m]).
rewrite sform_homogeneousE sform_extensionE sform_wordsE scalar_symmetric_form_evaluation.
by rewrite big_tuple.
Qed.
