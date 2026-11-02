(** Federer (1969), 3.1.24, p. 240: scalar
    polynomial maps in the inverse formula have continuous
    coefficients. Multilinearity supplies the scalar-source bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP TensorFamilyUP MultilinearFamilyAlgebra
  SymmetricForms ContinuousSymmetricFormAdapter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_symmetric_form_bound]: supporting the
    scalar polynomials in Federer 3.1.24, p. 240.
    Every symmetric form on the scalar line is bounded by
    its value on the tuple of ones times the product of
    the argument norms, including degree zero. *)
Lemma scalar_symmetric_form_bound (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_seminorm NY) (phi:S_m R^o Y m) :
  norm_bounded_symmetric_form (fun t:R^o=>`|t|) NY phi.
Proof.
pose ones:{ffun 'I_m->R^o}:=[ffun i=>(1:R^o)].
exists (NY (phi [tuple ones i | i<m])); split; first exact (real_seminorm_nonnegative hNY _).
move=>t.
pose u:{ffun 'I_m->R^o}:=[ffun i=>tnth t i].
have hh:=@multilinear_family_scale_all R m (fun _=>[the lmodType R of R^o]) Y
  (fun w:{ffun 'I_m->R^o}=>phi [tuple w i | i<m]) (sform_finite_family_multilinear phi) ones u.
have ht:[tuple [ffun i:'I_m=>u i*:ones i] j | j<m]= t.
  apply:eq_from_tnth=>i; rewrite tnth_mktuple ffunE /ones !ffunE.
  change (tnth t i*1=tnth t i); exact: mulr1.
rewrite ht in hh.
have hnorm:=congr1 NY hh.
rewrite (real_seminorm_scale hNY) normr_prod in hnorm.
rewrite hnorm mulrC.
have he:(\prod_(i<m) `|u i|)=\prod_(i<m) `|tnth t i|.
  by apply:eq_bigr=>i _; rewrite /u ffunE.
by rewrite he.
Qed.
