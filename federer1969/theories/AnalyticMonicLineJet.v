(** Federer (1969), 3.4.8(8), p. 330:
    an original monic coordinate relation
    has a nonzero positive directional
    derivative. Read its leading coefficient
    with the existing exact line-polynomial
    Taylor theorem from 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormAnalyticUP AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives AnalyticGermNeighbourhood AnalyticGermJetsSealed
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine AnalyticGermDirectionalCoefficient
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_monic_line_nonzero_directional_jet]:
    the monic relation used to recover
    each original B_j has nonzero highest
    directional coefficient, 3.4.8(8), p. 330.
    The actual analytic line-coefficient theorem
    proves the derivative; it is not
    supplied as a relation hypothesis. *)
Theorem analytic_monic_line_nonzero_directional_jet (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) (f:@analytic_representative_type R X NX hNX 0)
  k (v:X) (a:nat->R):
  (0<k)%N ->
  (forall t:R,analytic_representative_value f (t*:v) = t^+k+\sum_(i<k) a i*t^+(i:nat)) ->
  has_nonzero_analytic_directional_jet (analytic_germ f) v.
Proof.
move=>hK hLine.
pose NS:=fun z:R^o=>`|z|.
pose hNS:=@scalar_absolute_value_norm R.
pose F:=analytic_representative_value f.
have [U [hOrigin [_ [_ hAnalytic]]]]:=@analytic_germ_open_representative R X R^o NX NS hNX hNS
  setT F 0 (analytic_representative_analytic f).
have [c [hC _]]:=@analytic_directional_coefficient_exists R X R^o NX NS hNX hNS U F k v hAnalytic.
pose b:=fun j:nat=>if j==k then (1:R) else a j.
have hExact t (ht:`|t|<1):F (0+t*:v) = \sum_(j<k.+1) t^+j*:(b j:R^o).
  change (F (0+t*:v) = \sum_(j<k.+1) t^+j*b j).
  rewrite add0r /F hLine big_ord_recr /= /b eqxx mulr1 [t^+k+_]addrC.
  congr (_+t^+k);apply:eq_bigr=>j _.
  have hDifferent:((j:nat)!=k)%N by apply/eqP=>hEqual;have hSmall:=ltn_ord j;by rewrite hEqual ltnn in hSmall.
  by rewrite (negbTE hDifferent) mulrC.
have hValue:=@analytic_directional_polynomial_line_coefficient R X R^o NX NS hNX hNS
  U F k v 0 c k.+1 b 1 hOrigin hAnalytic hC ltr01 hExact.
have hLeading:c 0 = 1 by rewrite hValue ltnSn /b eqxx.
have hActual:=@analytic_directional_coefficient_at_germ_centre R X NX hNX 0 k
  (analytic_germ f) f U v c (erefl _) hOrigin hAnalytic hC.
exists k;split;first exact:hK.
move=>hZero.
rewrite /analytic_germ_directional_coefficient hZero mulr0 hLeading in hActual.
by move/eqP:hActual;rewrite oner_eq0.
Qed.
