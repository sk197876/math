(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    a positive-degree homogeneous polynomial has a nonzero
    analytic directional jet wherever its value is nonzero.
    Reuse the existing exact line-polynomial coefficient
    theorem, rather than redoing higher differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicGermFormsSealed HolomorphicGermFormsUP HolomorphicUP SymmetricForms HolomorphicGermDirectionalJetValue Hom RealNormUP NormAnalyticUP HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermRepresentatives HolomorphicGermNeighbourhood HolomorphicGermJetsSealed
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine HolomorphicGermDirectionalCoefficient
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicReductionLociUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_homogeneous_germ_direction]: the
    positive-order directional test of an actual leading
    polynomial used in 3.4.12, p. 339, extending 3.4.11, p. 338.
    Exact line coefficients prove that its kth
    normalized directional coefficient is its value at v. *)
Theorem holomorphic_homogeneous_germ_direction (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) (f:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0)
  k (P:X->ComplexScalars.C R) (v:X):
  (0<k)%N ->(forall x,holomorphic_representative_value f x= P x) ->
  (forall (t:R) x,P (t*:(x:restricted_space (ComplexScalars.embed R) X))=t^+k*:(P x:restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)) ->P v<>0 ->
  has_nonzero_holomorphic_directional_jet hNX (holomorphic_germ f) v.
Proof.
move=>hK hValues hScale hNonzero.
pose NS:=@complex_modulus R.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose hNS:=@complex_modulus_real_norm R.
pose F:=holomorphic_representative_value f.
have [U [hOrigin [_ [_ hHOL]]]]:=@holomorphic_germ_open_representative R X NX (complex_norm_real hNX) 0 f.
have hAnalytic:=hHOL.1.
have [c [hC _]]:=@analytic_directional_coefficient_exists R XR CR NX NS
  (complex_norm_real hNX) hNS U F k v hAnalytic.
pose b:=fun j:nat=>if j==k then P v else 0.
have hExact t (ht:`|t|<1):F (0+t*:(v:XR))=\sum_(j<k.+1) t^+j*:(b j:CR).
  rewrite add0r /F hValues hScale big_ord_recr /= /b eqxx.
  have hZero:(\sum_(j<k) t^+j*:((if (j:nat)==k then P v else 0):CR))=0.
    apply:big1=>j _.
    have hDifferent:((j:nat)!=k)%N by apply/eqP=>hEqual;have hSmall:=ltn_ord j;by rewrite hEqual ltnn in hSmall.
    by rewrite (negbTE hDifferent) scaler0.
  by rewrite hZero add0r.
have hValue:=@analytic_directional_polynomial_line_coefficient R XR CR NX NS (complex_norm_real hNX) hNS
  U F k v 0 c k.+1 b 1 hOrigin hAnalytic hC ltr01 hExact.
have hLeading:c 0= P v by rewrite hValue ltnSn /b eqxx.
have hActual:=@holomorphic_directional_coefficient_at_germ_centre R X NX hNX 0 k
  (holomorphic_germ f) f U v c (erefl _) hOrigin hAnalytic hC.
exists k;split;first exact:hK.
move=>hZero;apply:hNonzero.
have hJet:@ContinuousMultilinear.evaluation R k XR CR NX NS (complex_norm_real hNX) hNS
    [ffun _:'I_k=>v] (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 k (holomorphic_germ f))=0.
  have hEqual:=@HolomorphicGermForms.laws R X NX hNX 0 k (holomorphic_germ f) [tuple v|_<k].
  have hTuple:[ffun i=>tnth [tuple v|_<k] i]=[ffun _:'I_k=>v]
    by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
  rewrite hTuple hZero in hEqual;exact:esym hEqual.
rewrite (@holomorphic_germ_directional_coefficient_jet_value R X NX hNX 0 k (holomorphic_germ f) v)
  hJet mulr0 hLeading in hActual.
exact:hActual.
Qed.
