(** Federer (1969), 3.1.24, p. 238: the
    homogeneous series is centred at the actual point a.
    Translation preserves the exact higher differential fields. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  SymmetricForms HomogeneousPolynomialFunctions PolynomialTaylorTerms ContinuousSymmetricFormAdapter
  HomogeneousPolynomialDifferentials NormClassOneUP NormClassHigherUP NormClassHigherDerivative
  NormHigherDifferentialUP NormHigherDifferentialUnique NormClassInfinityPolynomial
  NormAffineDilationDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [shifted_homogeneous_differential_fields]: supporting
    the series of p_m(x-a) in Federer 3.1.24,
    p. 238. Translation by -a carries the actual
    differential fields of each homogeneous coefficient to the
    corresponding translated function, with no scaling of their
    values. Continuity is inherited from the proved smoothness
    of the translated polynomial. *)
Theorem shifted_homogeneous_differential_fields (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    m (phi:S_m X Y m) a :
  norm_bounded_symmetric_form NX NY phi ->
  exists D:forall i,X->Z i,
    (forall i x u,@ev i u (D i x)=
      symmetric_taylor_term i phi (x-a) [tuple u j | j<i]) /\
    (forall i x,has_norm_higher_differential NX ev ZN (fun _=>True)
      (fun y=>sform_polynomial_value phi (y-a)) i x (D i x)) /\
    forall i,norm_class_zero NX (@ZN i) (fun _=>True) (D i).
Proof.
move=>hphi.
have hopen x (_:True):norm_domain_interior NX (fun _=>True) x.
  exists 1; split; first exact ltr01; by move=>v hv.
have hfun:(fun y=>sform_polynomial_value phi (1*:y-a))=
    (fun y=>sform_polynomial_value phi (y-a)).
  by apply: funext=>y; rewrite scale1r.
have [E [he [hd hc]]]:=@homogeneous_polynomial_differential_fields R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) hopen m phi hphi.
pose D i x:=E i (x-a).
have hD i x:has_norm_higher_differential NX ev ZN (fun _=>True)
    (fun y=>sform_polynomial_value phi (y-a)) i x (D i x).
  have hh:=@norm_higher_differential_affine_dilation R X Y NX NY hNX hNY
    Z ev ZN hZ (sform_polynomial_value phi) 1 (-a) i (E i)
    (fun y=>hd i y Logic.I) x.
  rewrite expr1n !scale1r hfun in hh.
  exact hh.
have hraw:=@norm_class_infinity_sform_polynomial R X Y NX NY hNX hNY
  Z ev ZN hZ (fun _=>True) hopen m phi hphi.
have hshift:=@norm_class_infinity_affine_dilation R X Y NX NY hNX hNY Z ev ZN hZ
  (sform_polynomial_value phi) 1 (-a) hraw.
have hclass:norm_class_infinity NX NY ev ZN (fun _=>True)
    (fun y=>sform_polynomial_value phi (y-a)).
  by rewrite hfun in hshift.
exists D; split; first by move=>i x u; exact (he i (x-a) u).
split; first exact hD.
move=>i; have [_ [G [hG hCG]]]:=hclass i.
apply: (@norm_class_zero_domain_agreement R X (Z i) NX (@ZN i) (fun _=>True) G (D i) _ hCG).
move=>x hx; exact (@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ
  (fun _=>True) (fun y=>sform_polynomial_value phi (y-a)) i x (G x) (D i x) (hG x hx) (hD i x)).
Qed.
