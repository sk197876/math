(** Federer (1969), 3.4.12, p. 339: the original complex remainder
    has an actual finite transverse representative. Reuse actual holomorphic divided fields, the finite
    remainder calculation and original complex germ Taylor injectivity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormAnalyticUP HolomorphicUP HolomorphicLinear
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws
  AnalyticDirectionalCoefficient HolomorphicScalarDirectionalCoefficient
  ComplexWeierstrassTransverseUP ComplexWeierstrassCoefficientUP ComplexWeierstrassCoefficientExistence
  ComplexWeierstrassSplitInjective ComplexWeierstrassDivisionUP ComplexWeierstrassFiniteRemainderDomain
  ComplexWeierstrassFiniteRemainderCoefficients ComplexWeierstrassIteratedGermCoefficient
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearZero NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Reconstruction.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_finite_remainder_representation]: the
    actual finite expression has holomorphic coefficient fields on one
    original neighbourhood, and their values at zero are the original
    axis coefficients, extending 3.4.6, pp. 322–324, under 3.4.12,
    p. 339. All selected functions remain local existence witnesses. *)
Theorem complex_weierstrass_finite_remainder_representation v (xi:Hom X C^o)
    (inclusion:Hom K X) (projection:Hom X K) k
    (rho:holomorphic_germ_space hNXR (0:X)) (r:nat->nat->K->C):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  @norm_bounded_linear R XR CR NX N (complex_hom_real xi) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX rho v inclusion i j (r i j)) ->
  (forall i,(k<=i)%N ->forall j z,r i j z=0) ->
  exists g:@holomorphic_representative_type R X NX hNXR 0,holomorphic_germ g=rho /\
    exists U:set X,U 0 /\exists D:nat->X->C,
      (forall i,is_holomorphic hNXR hN U (D i)) /\
      (forall i,D i 0=r i 0%N (0:K)) /\
      forall x,holomorphic_representative_value g x=
        \sum_(i<k) (xi x)^+i*D i (inclusion (projection x)).
Proof.
move=>hSplit hXi hR hHigh.
have [f hRep]:=@holomorphic_germ_has_representative R X NX hNXR 0 rho.
pose F:=holomorphic_representative_value f.
have [U [haU hf]]:=holomorphic_representative_holomorphic f.
have hEach i:exists D:X->C,
    @is_analytic_directional_coefficient R XR CR NX N hNXR hN U F i v D /\
    is_holomorphic hNXR hN U D.
  exact:(@holomorphic_scalar_directional_coefficient_exists R X NX hNX U F i v hf).
have [D hD]:=choice hEach.
have [A [haA [hAU [hOpen hFinite]]]]:=@complex_weierstrass_finite_remainder_domain R X K NX NK hNX
  v xi inclusion projection U F k D hSplit hXi haU hf (fun i=>(hD i).2).
pose G:=fun x=>\sum_(i<k) (xi x)^+i*D i (inclusion (projection x)).
have [g hG]:=@holomorphic_representative_from_domain R X NX hNXR 0 A G haA hFinite.
pose beta:=holomorphic_germ g.
have [s hS]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX beta v inclusion.
have hg:is_holomorphic hNXR hN A (holomorphic_representative_value g) by rewrite hG.
have hCoefficients:=@complex_weierstrass_finite_remainder_coefficients R X K NX NK hNX
  v xi inclusion projection k rho beta f g U A D r s hSplit hRep (erefl _) haU haA hf.1 hg.1
  (fun i=>conj (hD i).1 (hD i).2.1) (fun x=>congr1 (fun H:X->C=>H x) hG) hR hS.
have hEqual:rho=beta.
  apply:(@complex_weierstrass_split_coefficients_injective R X K NX NK hNX v xi inclusion projection
    rho beta r s hSplit hR hS)=>i j z.
  rewrite hCoefficients;case hi:(i<k)%N=>//.
  have hLarge:(k<=i)%N by rewrite leqNgt hi.
  exact:hHigh i hLarge j z.
exists g;split;first exact:esym hEqual.
exists U;split;first exact:haU.
exists D;split;first by move=>i;exact:(hD i).2.
split;last by move=>x;rewrite hG.
move=>i.
have hCoefficientZero:@is_analytic_directional_coefficient R XR CR NX N hNXR hN
    U (D i) 0%N (inclusion (0:K)) (D i).
  move=>x hx z hz;rewrite invr1 scale1r.
  rewrite (zero_arity_arguments_unique [ffun _:'I_0=>inclusion (0:K)] [ffun _:'I_0=>(0:X)]).
  exact:esym hz.2.
have hOriginal:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX rho f U v inclusion
  i 0%N (r i 0%N) (D i) (D i) (0:K) hRep haU hf.1 (hR i 0%N) (hD i).1 hCoefficientZero.
exact:esym hOriginal.
Qed.
End Reconstruction.
