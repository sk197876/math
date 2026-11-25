(** Supporting Federer (1969), 3.4.8(5), p. 328:
    a basis-weighted sum of the actual radial
    quotient coefficients recovers the successor
    coefficient of the original germ. This is
    Taylor contraction from 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import Hom RealNormUP LinearBasis FiniteDualDimension SymmetricForms PolynomialTaylorTerms
  PolynomialTaylorTermContinuity ContinuousMultilinearUP ContinuousMultilinearSealed
  AnalyticGermRing AnalyticGermJetsSealed AnalyticGermCoefficientForms
  AnalyticGermDirectionalCoefficient AnalyticRadialQuotientUP AnalyticRadialQuotientSealed
  SuccessorTaylorContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_radial_coefficient_basis_sum]:
    summing the actual quotient coefficients against
    the original dual coordinates gives the original
    successor Taylor coefficient, supporting the expanded
    factorisation argument of 3.4.8(5), p. 328. *)
Lemma analytic_radial_coefficient_basis_sum (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) a n (b:'I_n->X) (hb:is_basis b)
  (alpha:@analytic_germ_ring R X NX hNX a) m x:
  \sum_(j<n) dual_basis hb j x *
    @analytic_germ_directional_coefficient R X NX hNX a m
      (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j)) x =
    @analytic_germ_directional_coefficient R X NX hNX a m.+1 alpha x.
Proof.
have [phi [hPhi _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
pose u:m.-tuple X:=[tuple x | i<m].
have hU:[tuple [ffun _:'I_m=>x] i | i<m] = u.
  apply:eq_from_tnth=>i;by rewrite /u !tnth_mktuple ffunE.
have hTerm j:
    dual_basis hb j x * @analytic_germ_directional_coefficient R X NX hNX a m
      (@AnalyticRadialQuotient.map R X NX hNX a alpha (b j)) x =
    (((m`!)%:R:R)^-1*((m.+1)%:R:R)^-1)*
      (dual_basis hb j x*:symmetric_taylor_term m (phi m.+1) (b j) u).
  rewrite /analytic_germ_directional_coefficient
    (@AnalyticRadialQuotient.laws R X NX hNX a alpha (b j) m (phi m.+1) (hPhi m.+1)) hU.
  change (dual_basis hb j x*(((m`!)%:R:R)^-1*(((m.+1)%:R:R)^-1*
    symmetric_taylor_term m (phi m.+1) (b j) u)) =
    (((m`!)%:R:R)^-1*((m.+1)%:R:R)^-1)*
      (dual_basis hb j x*symmetric_taylor_term m (phi m.+1) (b j) u)).
  ring.
under eq_bigr do rewrite hTerm.
rewrite -mulr_sumr (successor_taylor_contraction_basis_sum (phi m.+1) u hb x).
have hDiagonal:symmetric_taylor_term m (phi m.+1) x u = phi m.+1 [tuple x | i<m.+1].
  rewrite (symmetric_taylor_term_tuple_value (leqnSn m)).
  have hSmall:(m.+1-m)%N = 1%N by rewrite subSn // subnn.
  have hFactor:(((m.+1-m)`!)%:R:R)^-1 = 1 by rewrite hSmall /= invr1.
  rewrite hFactor scale1r;congr (phi m.+1 _);apply:val_inj.
  change ((tcast (subnKC (leqnSn m)) [tuple of u++[tuple x | i<m.+1-m]]:seq X)
    = ([tuple x | i<m.+1]:seq X)).
  have hConstant (l:nat):[seq x | i<-enum 'I_l] = nseq l x.
    have hMap (T:Type) (s:seq T):[seq x | i<-s] = nseq (size s) x.
      by elim:s=>[|i s ih] //=;rewrite ih.
    by rewrite hMap size_enum_ord.
  rewrite val_tcast /= hSmall /u !hConstant.
  by rewrite -nseqD addn1.
rewrite hDiagonal hPhi /analytic_germ_directional_coefficient.
have hTuple:[ffun i=>tnth [tuple x | i<m.+1] i] = [ffun _:'I_m.+1=>x].
  by apply/ffunP=>i;rewrite ffunE tnth_mktuple ffunE.
rewrite hTuple factS natrM invfM.
ring.
Qed.
