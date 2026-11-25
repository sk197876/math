(** Federer (1969), 3.1.24, p. 239: all
    actual derivatives of the rational scalar majorants. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP NormClassOneUP NormClassHigherUP
  NormClassHigherArithmetic ContinuousMultilinearUP ContinuousMultilinearZero
  NormHigherDifferentialUP NormHigherDifferentialConstant NormHigherDifferentialArithmetic
  NormAffineDomainDifferentials ScalarReciprocalHigherDifferentials ScalarReciprocalContinuousFields
  ScalarAnalyticFraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_fraction_differentials]: the
    calculation of D^j f(0)=c^j j! for f(x)=cx/(1-cx)
    in Federer 3.1.24, p. 239. The function is
    smooth on its nonzero-denominator domain. Every displayed
    coefficient is identified with an actual recursive differential
    through affine substitution in the reciprocal, followed by
    addition of the constant -1. No analyticity or convergence
    assertion is used to assume the derivative formula. *)
Theorem scalar_analytic_fraction_differentials (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun x:R^o=>`|x|) (fun x:R^o=>`|x|)
      (@ev i) (@ZN i)) c :
  norm_class_infinity (fun x:R^o=>`|x|) (fun x:R^o=>`|x|) ev ZN
    (scalar_analytic_fraction_domain c) (scalar_analytic_fraction c) /\
  exists D:forall i,R->Z i,
    (forall i x,scalar_analytic_fraction_domain c x ->
      has_norm_higher_differential (fun x:R^o=>`|x|) ev ZN
        (scalar_analytic_fraction_domain c) (scalar_analytic_fraction c) i x (D i x)) /\
    forall i,(1<=i)%N -> forall u,@ev i u (D i 0)=
      (\prod_(j<i) u j)*(c^+i*(i`!)%:R).
Proof.
pose N:=fun x:R^o=>`|x|.
have hN:=scalar_absolute_value_norm R.
pose NZ:=fun x:R^o=>x!=0.
have hf:=scalar_reciprocal_class_infinity hZ.
have hA x (hx:NZ x):norm_domain_interior N NZ x:=((hf 0%N).1 x hx).1.
pose A:=scalar_analytic_fraction_domain c.
have hopen x (hx:A x):norm_domain_interior N A x.
  exact (@norm_affine_preimage_interior R R^o N hN NZ hA (-c) 1 x hx).
have hpre:=@norm_class_infinity_affine_precomposition R R^o R^o N N hN hN
  Z ev ZN hZ NZ hA (fun x=>x^-1) (-c) 1 hf.
have hconst:=@norm_class_infinity_constant R R^o R^o N N hN hN Z ev ZN hZ A hopen (-1).
have hregular:norm_class_infinity N N ev ZN A (scalar_analytic_fraction c).
  move=>k; exact (norm_class_higher_add hN hN hZ (hpre k) (hconst k)).
split; first exact hregular.
have [E [hE [hcE heE]]]:=@scalar_reciprocal_continuous_fields R Z ev ZN hZ.
have [z0 hz0]:=continuous_multilinear_zero_surjective hN (hZ 0%N) (-1).
pose K j:=@constant_higher_form R Z z0 j.
have hK j x (hx:A x):has_norm_higher_differential N ev ZN A (fun _=>-1) j x (K j).
  exact (@norm_higher_differential_constant R R^o R^o N N hN hN Z ev ZN hZ A hopen
    (-1) z0 hz0 j x hx).
pose H j x:=(-c)^+j*:E j (-c*x+1).
have hH j x (hx:A x):has_norm_higher_differential N ev ZN A
    (fun y=>(-c*y+1)^-1) j x (H j x).
  exact (@norm_higher_differential_affine_precomposition R R^o R^o N N hN hN
    Z ev ZN hZ NZ hA (fun x=>x^-1) (-c) 1 j (E j) (hE j) x hx).
pose D j x:=H j x+K j.
have hD j x (hx:A x):has_norm_higher_differential N ev ZN A (scalar_analytic_fraction c) j x (D j x).
  exact (@norm_higher_differential_field_add R R^o R^o N N hN hN Z ev ZN hZ A j
    (fun y=>(-c*y+1)^-1) (fun _=>-1) (H j) (fun _=>K j) (hH j) (hK j) x hx).
exists D; split; first exact hD.
move=>[|j] hj u; first by [].
have hOne:(1:R)!=0 by rewrite oner_eq0.
have he:=heE j.+1 1 hOne u.
rewrite /D /H /K /constant_higher_form linearD /= linear0 addr0 linearZ /= mulr0 add0r he.
rewrite /scalar_reciprocal_derivative_coefficient invr1 expr1n mulr1.
change ((-c)^+j.+1*((\prod_(i<j.+1) u i)*((-1)^+j.+1*((j.+1)`!)%:R))=
  (\prod_(i<j.+1) u i)*(c^+j.+1*((j.+1)`!)%:R)).
have hs:(-c)^+j.+1*(-1)^+j.+1= c^+j.+1.
  by rewrite -exprMn mulrN mulr1 opprK.
have hid:(-c)^+j.+1*((\prod_(i<j.+1) u i)*((-1)^+j.+1*((j.+1)`!)%:R))=
    ((-c)^+j.+1*(-1)^+j.+1)*((\prod_(i<j.+1) u i)*((j.+1)`!)%:R) by ring.
rewrite hid hs; ring.
Qed.
