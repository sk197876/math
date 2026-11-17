(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: an original monic complex coordinate relation
    has a nonzero positive directional derivative. Apply the existing
    normed-target Taylor coefficient uniqueness theorem on the real line. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  NormAnalyticUP NormAnalyticLocal HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives HolomorphicGermFormsSealed HolomorphicGermDirectionalCoefficient
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine HolomorphicReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_monic_line_nonzero_directional_jet]: the
    actual highest coefficient equals one, so the original positive
    directional derivative is nonzero, 3.4.12, p. 339. *)
Theorem holomorphic_monic_line_nonzero_directional_jet (R:realType)
  (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
  (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0)
  k (v:X) (a:nat->ComplexScalars.C R):
  (0<k)%N ->
  (forall t:ComplexScalars.C R,holomorphic_representative_value f (t*:v)=
    t^+k+\sum_(i<k) a i*t^+(i:nat)) ->
  has_nonzero_holomorphic_directional_jet hNX (holomorphic_germ f) v.
Proof.
move=>hK hLine.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose C:=ComplexScalars.C R.
pose CR:=restricted_space (ComplexScalars.embed R) C^o.
pose hNXR:=complex_norm_real hNX.
pose N:=@complex_modulus R.
pose hN:=@complex_modulus_real_norm R.
pose F:=holomorphic_representative_value f.
have [U [hOrigin [hAnalytic _]]]:=holomorphic_representative_holomorphic f.
have [c [hC _]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U F k v hAnalytic.
pose b:=fun j:nat=>if j==k then (1:C) else a j.
have hExact t (ht:`|t|<1):F ((0:XR)+t*:(v:XR))=\sum_(j<k.+1) t^+j*:(b j:CR).
  rewrite add0r /F hLine big_ord_recr /= /b eqxx.
  change ((ComplexScalars.embed R t)^+k+\sum_(i<k) a i*(ComplexScalars.embed R t)^+(i:nat)=
    (\sum_(j<k) ComplexScalars.embed R (t^+j)*(if ((j:nat)==k)%N then 1 else a j))+
      ComplexScalars.embed R (t^+k)*1).
  rewrite mulr1 rmorphXn [_^+k+_]addrC.
  congr (_+(ComplexScalars.embed R t)^+k);apply:eq_bigr=>j _.
  have hDifferent:((j:nat)!=k)%N by apply/eqP=>hEqual;have hSmall:=ltn_ord j;by rewrite hEqual ltnn in hSmall.
  by rewrite (negbTE hDifferent) rmorphXn mulrC.
have hValue:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN
  U F k v 0 c k.+1 b 1 hOrigin hAnalytic hC ltr01 hExact.
have hLeading:c 0 = 1 by rewrite hValue ltnSn /b eqxx.
have hActual:=@holomorphic_directional_coefficient_at_germ_centre R X NX hNX 0 k
  (holomorphic_germ f) f U v c (erefl _) hOrigin hAnalytic hC.
exists k;split;first exact:hK.
move=>hZero.
rewrite /holomorphic_germ_directional_coefficient sform_polynomial_diagonal_value hZero scaler0 in hActual.
by rewrite hLeading in hActual;move/eqP:hActual;rewrite oner_eq0.
Qed.
