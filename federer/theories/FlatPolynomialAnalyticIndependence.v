(** Federer (1969), 3.4.5, p. 321: finite
    polynomial relations in the actual flat exponential have
    zero analytic coefficient germs. This is the internal
    real Taylor argument for the example cited to Cartan
    (1957), pp. 97–99, rather than a transcendence axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology NormAnalyticUP
  FiniteAnalyticCoefficientBound FlatExponentialSealed FlatExponentialOrder
  FlatPolynomialConstantBound ScalarRightFlatAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [flat_polynomial_analytic_coefficients_vanish]:
    actual finite analytic coefficient independence at the
    flat endpoint, supporting the example cited at 3.4.5,
    p. 321. Finite boundedness and the proved actual
    Taylor theorem give the zero constant germ; division
    uses only the strictly positive original flat coefficient. *)
Theorem flat_polynomial_analytic_coefficients_vanish (R:realType) N (f:nat->R->R) (r:R):
  (forall i,(i<N)%N ->@norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) setT (f i) 0) ->
  0<r ->
  (forall t:R,0<t<r ->(\sum_(i<N) f i t*(FlatExponential.value t)^+i)=0) ->
  forall i,(i<N)%N ->exists d:R,0<d /\forall t:R,`|t|<d ->f i t=0.
Proof.
elim:N f r=>[|N ih] f r hAnalytic hr hRelation i hi;first by [].
pose Nrm:=fun t:R^o=>`|t|.
pose hNrm:=@scalar_absolute_value_norm R.
have hFinite (j:'I_N.+1):@norm_analytic_at R R^o R^o Nrm Nrm hNrm hNrm setT (f j) 0.
  exact:hAnalytic j (valP j).
have [s [C [hs [hC hBound]]]]:=@finite_analytic_coefficient_bound R
  (Finite.clone 'I_N.+1 _) (fun j=>f j) hFinite.
pose rho:R:=Num.min r s.
have hRho:0<rho by rewrite /rho lt_min hr hs.
have hRhoR:rho<=r by rewrite /rho ge_min lexx.
have hRhoS:rho<=s by rewrite /rho ge_min lexx orbT.
have hTailIndex j (hj:(j<N)%N):(j.+1<N.+1)%N by rewrite ltnS.
have hConstant t (ht:0<t<rho):`|f 0%N t|<=(N%:R*C)*FlatExponential.value t.
  have htr:0<t<r:=introT andP (conj (andP ht).1 (lt_le_trans (andP ht).2 hRhoR)).
  have hts:0<t<s:=introT andP (conj (andP ht).1 (lt_le_trans (andP ht).2 hRhoS)).
  exact:(@flat_polynomial_constant_bound R N (fun j=>f j t) (FlatExponential.value t) C
    (@flat_exponential_nonnegative R t) (@flat_exponential_unit_bound R t) (ltW hC)
    (fun j hj=>hBound t hts (Ordinal (hTailIndex j hj))) (hRelation t htr)).
have hMultiplier:0<=(N%:R:R)*C:=mulr_ge0 (ler0n R N) (ltW hC).
have [U [hU0 [_ [hUOpen hUValue]]]]:=@analytic_bounded_flat_exponential_locally_zero R
  setT (f 0%N) (N%:R*C) rho (hAnalytic 0%N (leq0n N)) hMultiplier hRho hConstant.
have hInterior:=(@norm_domain_interior_neighbourhood R R^o Nrm hNrm U 0).2
  (open_nbhs_nbhs (conj hUOpen hU0)).
have [d [hd hBall]]:=hInterior.
have hZero t (ht:`|t|<d):f 0%N t=0.
  have hUt:=hBall t ht;rewrite add0r in hUt;exact:hUValue t hUt.
case:i hi=>[|i] hi;first by exists d;split.
pose sigma:R:=Num.min r d.
have hSigma:0<sigma by rewrite /sigma lt_min hr hd.
have hSigmaR:sigma<=r by rewrite /sigma ge_min lexx.
have hSigmaD:sigma<=d by rewrite /sigma ge_min lexx orbT.
have hTailAnalytic j (hj:(j<N)%N):@norm_analytic_at R R^o R^o Nrm Nrm hNrm hNrm setT (f j.+1) 0.
  exact:hAnalytic j.+1 hj.
have hTailRelation t (ht:0<t<sigma):(\sum_(j<N) f (val j).+1 t*(FlatExponential.value t)^+j)=0.
  have htr:0<t<r:=introT andP (conj (andP ht).1 (lt_le_trans (andP ht).2 hSigmaR)).
  have htd:`|t|<d by rewrite ger0_norm ?(ltW (andP ht).1) //;exact:lt_le_trans (andP ht).2 hSigmaD.
  have hSum:=hRelation t htr.
  rewrite big_ord_recl /= (hZero t htd) mul0r add0r in hSum.
  have hFactor:(\sum_(j<N) f (val j).+1 t*(FlatExponential.value t)^+(val j).+1)=
      FlatExponential.value t*\sum_(j<N) f (val j).+1 t*(FlatExponential.value t)^+j.
    rewrite mulr_sumr;apply:eq_bigr=>j _;rewrite exprS;ring.
  rewrite hFactor in hSum.
  have hPositive:0<FlatExponential.value t by rewrite flat_exponential_positive;exact:(andP ht).1.
  by move/eqP:hSum;rewrite mulf_eq0 (gt_eqF hPositive) /= =>/eqP.
exact:(@ih (fun j=>f j.+1) sigma hTailAnalytic hSigma hTailRelation i hi).
Qed.
