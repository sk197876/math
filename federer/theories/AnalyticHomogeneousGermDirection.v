(** Federer (1969), 3.4.11, p. 338:
    a positive-degree homogeneous polynomial has a nonzero
    analytic directional jet wherever its value is nonzero.
    Reuse the existing exact line-polynomial coefficient
    theorem, rather than redoing higher differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives AnalyticGermNeighbourhood AnalyticGermJetsSealed
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine AnalyticGermDirectionalCoefficient
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_homogeneous_germ_direction]: the
    positive-order directional test of an actual leading
    polynomial used in 3.4.11, p. 338.
    Exact line coefficients prove that its kth
    normalized directional coefficient is its value at v. *)
Theorem analytic_homogeneous_germ_direction (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) (f:@analytic_representative_type R X NX hNX 0)
  k (P:X->R) (v:X):
  (0<k)%N ->(forall x,analytic_representative_value f x= P x) ->
  (forall (t:R) x,P (t*:x)=t^+k*P x) ->P v<>0 ->
  has_nonzero_analytic_directional_jet (analytic_germ f) v.
Proof.
move=>hK hValues hScale hNonzero.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose F:=analytic_representative_value f.
have [U [hOrigin [_ [_ hAnalytic]]]]:=@analytic_germ_open_representative R X R^o NX NS hNX hNS
  setT F 0 (analytic_representative_analytic f).
have [c [hC _]]:=@analytic_directional_coefficient_exists R X R^o NX NS hNX hNS U F k v hAnalytic.
pose b:=fun j:nat=>if j==k then P v else 0.
have hExact t (ht:`|t|<1):F (0+t*:v)=\sum_(j<k.+1) t^+j*:(b j:R^o).
  change (F (0+t*:v)=\sum_(j<k.+1) t^+j*b j).
  rewrite add0r /F hValues hScale big_ord_recr /= /b eqxx.
  have hZero:(\sum_(j<k) t^+j*(if (j:nat)==k then P v else 0))=0.
    apply:big1=>j _.
    have hDifferent:((j:nat)!=k)%N by apply/eqP=>hEqual;have hSmall:=ltn_ord j;by rewrite hEqual ltnn in hSmall.
    by rewrite (negbTE hDifferent) mulr0.
  by rewrite hZero add0r.
have hValue:=@analytic_directional_polynomial_line_coefficient R X R^o NX NS hNX hNS
  U F k v 0 c k.+1 b 1 hOrigin hAnalytic hC ltr01 hExact.
have hLeading:c 0= P v by rewrite hValue ltnSn /b eqxx.
have hActual:=@analytic_directional_coefficient_at_germ_centre R X NX hNX 0 k
  (analytic_germ f) f U v c (erefl _) hOrigin hAnalytic hC.
exists k;split;first exact:hK.
move=>hZero;apply:hNonzero.
rewrite /analytic_germ_directional_coefficient hZero mulr0 hLeading in hActual.
exact:hActual.
Qed.
