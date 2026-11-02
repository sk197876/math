(** Federer (1969), 3.1.24, p. 240: the scalar
    forward majorant has first derivative beta*gamma at zero
    and higher derivatives -gamma^m m!, as used to identify
    the inverse-majorant recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import TensorUP Hom RealNormUP NormDifferentialUP NormClassOneUP NormClassHigherUP
  NormClassHigherArithmetic NormClassHigherLocalValues ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialArithmetic
  ScalarAffineDifferentials ScalarAnalyticFraction ScalarAnalyticFractionDifferentials ScalarInverseMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_forward_majorant_coefficient]: the
    scalar derivative coefficients at zero of the rational
    g in Federer 3.1.24, p. 240. The first is
    beta*gamma; positive orders above one are -gamma^m m!.
    The constant coefficient is zero. *)
Definition scalar_forward_majorant_coefficient (R:realType) (b g:R) m:R :=
  match m with 0%N=>0 | 1%N=>b*g | _=> -(g^+m*(m`!)%:R) end.

(** Source for [scalar_forward_majorant_differentials]: the
    printed scalar g has actual smooth differential fields
    on its nonzero-denominator domain, with its displayed
    coefficients at zero, supporting the inverse recurrence
    in Federer 3.1.24, p. 240. The proof uses
    the previously proved affine and rational derivatives. *)
Theorem scalar_forward_majorant_differentials (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (@ev i) (@ZN i))
    (b g:R) :
  norm_class_infinity (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) ev ZN
    (scalar_analytic_fraction_domain g) (scalar_forward_majorant b g) /\
  exists D:forall i,R->Z i,
    (forall i x,scalar_analytic_fraction_domain g x -> has_norm_higher_differential
      (fun t:R^o=>`|t|) ev ZN (scalar_analytic_fraction_domain g) (scalar_forward_majorant b g) i x (D i x)) /\
    forall i,(1<=i)%N -> forall u,@ev i u (D i 0)=
      (\prod_(j<i) u j)*scalar_forward_majorant_coefficient b g i.
Proof.
pose N:=fun t:R^o=>`|t|.
pose hN:=scalar_absolute_value_norm R.
pose A:=scalar_analytic_fraction_domain g.
have [hFrac [F [hF hFe]]]:=@scalar_analytic_fraction_differentials R Z ev ZN hZ g.
have hopen x (hx:A x):norm_domain_interior N A x:=((hFrac 0%N).1 x hx).1.
have [hLin [L [hL [hLe hLc]]]]:=@scalar_affine_higher_differentials R Z ev ZN hZ A hopen ((b+1)*g) 0.
pose H:=fun x=>((b+1)*g*x+0)+(-1)*scalar_analytic_fraction g x.
have hEq x (_:A x):H x= scalar_forward_majorant b g x.
  by rewrite /H /scalar_forward_majorant addr0 mulN1r.
have hReg:norm_class_infinity N N ev ZN A (scalar_forward_majorant b g).
  move=>k.
  have hneg:=@norm_class_higher_scale R R^o R^o N N hN hN Z ev ZN hZ A k
    (scalar_analytic_fraction g) (-1) (hFrac k).
  have hs:=@norm_class_higher_add R R^o R^o N N hN hN Z ev ZN hZ A k
    (fun x=>(b+1)*g*x+0) (fun x=>(-1)*scalar_analytic_fraction g x) (hLin k) hneg.
  exact (@norm_class_higher_domain_agreement R R^o R^o N N hN hN Z ev ZN hZ A H
    (scalar_forward_majorant b g) k hEq hs).
split; first exact hReg.
pose D i x:=L i x+(-1)*:F i x.
have hD i x (hx:A x):has_norm_higher_differential N ev ZN A (scalar_forward_majorant b g) i x (D i x).
  have hneg:=@norm_higher_differential_field_scale R R^o R^o N N hN hN Z ev ZN hZ A i
    (scalar_analytic_fraction g) (F i) (-1) (hF i).
  have hs:=@norm_higher_differential_field_add R R^o R^o N N hN hN Z ev ZN hZ A i
    (fun x=>(b+1)*g*x+0) (fun x=>(-1)*scalar_analytic_fraction g x) (L i)
    (fun x=>(-1)*:F i x) (hL i) hneg x hx.
  exact ((@norm_higher_differential_local_agreement R R^o R^o N N hN hN Z ev ZN hZ
    i A A A H (scalar_forward_majorant b g) hopen (fun x hx=>iff_refl _) (fun x hx _=>hEq x hx)
    x hx (D i x)).1 hs).
exists D; split; first exact hD.
move=>i hi u.
rewrite /D linearD linearZ /= (hLe i 0 u) (hFe i hi u).
case:i hi u=>[|[|i]] hi u; first by [].
- rewrite /scalar_affine_derivative_coefficient /scalar_forward_majorant_coefficient expr1 /= ?mulr1.
  change ((\prod_(j<1) u j)*((b+1)*g)+(-1)*((\prod_(j<1) u j)*g)=
    (\prod_(j<1) u j)*(b*g)); ring.
- rewrite /scalar_affine_derivative_coefficient /scalar_forward_majorant_coefficient mulr0 add0r.
  change ((-1:R)*((\prod_(j<i.+2) u j)*(g^+i.+2*((i.+2)`!)%:R))=
    (\prod_(j<i.+2) u j)*(-(g^+i.+2*((i.+2)`!)%:R))).
  ring.
Qed.
