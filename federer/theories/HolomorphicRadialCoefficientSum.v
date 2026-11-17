(** Federer (1969), 3.4.12, p. 339, extending the
    ideal-power argument of 3.4.8(5), p. 328: the original
    complex basis reconstructs the successor Taylor coefficient from
    actual radial quotients. Reuse the scalar-independent successor
    contraction and original complex dual-basis expansion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP LinearBasis FiniteDualDimension
  SymmetricForms PolynomialDiagonalNorm PolynomialTaylorTerms PolynomialTaylorTermContinuity SuccessorTaylorContraction
  HolomorphicGermRing HolomorphicGermFormsSealed HolomorphicGermDirectionalCoefficient
  HolomorphicGermDirectionalJetValue HolomorphicRadialQuotientUP HolomorphicRadialQuotientSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_radial_coefficient_basis_sum]: summing
    actual quotient coefficients against the original complex dual
    coordinates gives the original successor coefficient, extending
    Taylor contraction in 1.10.4, p. 46, under 3.4.12, p. 339. *)
Lemma holomorphic_radial_coefficient_basis_sum (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX) a n
    (b:'I_n->X) (hb:is_basis b)
    (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a) m x:
  \sum_(j<n) dual_basis hb j x*@holomorphic_germ_directional_coefficient R X NX hNX a m
    (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j)) x=
      @holomorphic_germ_directional_coefficient R X NX hNX a m.+1 alpha x.
Proof.
pose C:=ComplexScalars.C R.
pose phi k:=@HolomorphicGermForms.value R X NX hNX a k alpha.
have hPhi k:=@HolomorphicGermForms.laws R X NX hNX a k alpha.
pose u:m.-tuple X:=[tuple x|_<m].
have hU:[tuple [ffun _:'I_m=>x] i|i<m]=u.
  apply:eq_from_tnth=>i;by rewrite /u !tnth_mktuple ffunE.
have hTerm j:dual_basis hb j x*@holomorphic_germ_directional_coefficient R X NX hNX a m
    (@HolomorphicRadialQuotient.map R X NX hNX a alpha (b j)) x=
      (((m`!)%:R:C)^-1*((m.+1)%:R:C)^-1)*
        (dual_basis hb j x*:symmetric_taylor_term m (phi m.+1) (b j) u).
  rewrite holomorphic_germ_directional_coefficient_jet_value
    (@HolomorphicRadialQuotient.laws R X NX hNX a alpha (b j) m (phi m.+1) (hPhi m.+1)) hU.
  change (dual_basis hb j x*(((m`!)%:R:C)^-1*(((m.+1)%:R:C)^-1*
      symmetric_taylor_term m (phi m.+1) (b j) u))=
    (((m`!)%:R:C)^-1*((m.+1)%:R:C)^-1)*
      (dual_basis hb j x*symmetric_taylor_term m (phi m.+1) (b j) u)).
  ring.
under eq_bigr do rewrite hTerm.
rewrite -mulr_sumr (successor_taylor_contraction_basis_sum (phi m.+1) u hb x).
have hDiagonal:symmetric_taylor_term m (phi m.+1) x u=phi m.+1 [tuple x|_<m.+1].
  rewrite (symmetric_taylor_term_tuple_value (leqnSn m)).
  have hSmall:(m.+1-m)%N = 1%N by rewrite subSn // subnn.
  have hFactor:(((m.+1-m)`!)%:R:C)^-1 = 1 by rewrite hSmall /= invr1.
  rewrite hFactor scale1r;congr (phi m.+1 _);apply:val_inj.
  change ((tcast (subnKC (leqnSn m)) [tuple of u++[tuple x|_<m.+1-m]]:seq X)=
    ([tuple x|_<m.+1]:seq X)).
  have hConstant l:[seq x|i<-enum 'I_l]=nseq l x.
    have hMap (T:Type) (s:seq T):[seq x|i<-s]=nseq (size s) x.
      by elim:s=>[|i s ih] //=;rewrite ih.
    by rewrite hMap size_enum_ord.
  rewrite val_tcast /= hSmall /u !hConstant.
  by rewrite -nseqD addn1.
rewrite hDiagonal /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value.
change ((((m`!)%:R:C)^-1*((m.+1)%:R:C)^-1)*phi m.+1 [tuple x|_<m.+1]=
  (((m.+1)`!)%:R:C)^-1*phi m.+1 [tuple x|_<m.+1]).
rewrite factS natrM invfM;ring.
Qed.
