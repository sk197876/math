(** Federer (1969), 3.4.5, p. 319: the
    homogeneous-series realisation has the prescribed derivative
    coefficients at its centre. The contraction is that of
    1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm SymmetricForms PolynomialTaylorTerms SymmetricTaylorOrigin.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Origin.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Variable phi:forall m,S_m X Y m.
Variable w:forall i,Z i.
Variable a:X.
Variable E:forall m:nat,forall i,X->Z i.
Hypothesis hPhi:forall i (u:{ffun 'I_i->X}),phi i [tuple u j | j<i]=ev i u (w i).
Hypothesis hEval:forall m i x u,ev i u (E m i x)=
  symmetric_taylor_term i (phi m) (x-a) [tuple u j | j<i].

(** Source for [analytic_form_series_centre_term]: the i-th
    derivative of the m-th homogeneous Taylor term at its
    centre is zero unless i=m, when it is the original
    i-form; 3.4.5, p. 319. *)
Lemma analytic_form_series_centre_term m i:
  E m i a=if m==i then w i else 0.
Proof.
apply:(continuous_multilinear_extensional (hZ i))=>u.
rewrite hEval subrr.
case hEqual:(m==i).
- move/eqP:hEqual=>hEqual;subst m.
  by rewrite symmetric_taylor_origin_same_degree hPhi.
- have hDifferent:m!=i by rewrite hEqual.
  move:hDifferent;rewrite neq_ltn;move/orP=>[hLess|hGreater].
  + by rewrite (symmetric_taylor_term_above_degree _ _ hLess) sform_zeroE linear0.
  + by rewrite (symmetric_taylor_origin_lower_degree _ hGreater) sform_zeroE linear0.
Qed.

(** Source for [analytic_form_series_centre_prefix]: after
    order i has entered the derivative-series prefix, its
    value at the centre is exactly the original i-form;
    supporting analytic realisation in 3.4.5, p. 319. *)
Lemma analytic_form_series_centre_prefix i N:(i<N)%N ->
  (\sum_(m<N) E m i a)=w i.
Proof.
move=>hIN.
have hTerm m:E m i a=if m==i then w i else 0.
  exact:analytic_form_series_centre_term.
under eq_bigr do rewrite hTerm.
have hOrdinal:i=val (Ordinal hIN) by [].
rewrite hOrdinal.
under eq_bigr do rewrite val_eqE.
by rewrite (bigD1 (Ordinal hIN)) //= eqxx big1 ?addr0 // =>m /negPf hm;rewrite hm.
Qed.
End Origin.
