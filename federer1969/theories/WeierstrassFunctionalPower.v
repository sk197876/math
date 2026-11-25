(** Federer (1969), 3.4.6(2), p. 322: the
    original monic coordinate power used as the dividend
    in the preparation proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormAnalyticUP NormAnalyticLinear
  NormAnalyticScalarProducts AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  AnalyticDirectionalCoefficient AnalyticDirectionalPolynomialLine AnalyticIteratedDirectionalCoefficients
  WeierstrassTransverseUP WeierstrassTransverseLaws WeierstrassCoefficientUP WeierstrassIteratedGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_functional_power_representative]:
    the actual function xi^k is analytic on the original
    whole space, supporting 3.4.6(2), p. 322.
    It is an existence witness for the original dividend. *)
Theorem weierstrass_functional_power_representative (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (xi:Hom X R^o) k:
  norm_bounded_linear NX (fun r:R^o=>`|r|) xi ->
  exists f:analytic_representative_type hNX (0:X),
    analytic_representative_value f=(fun x=>(xi x)^+k) /\
    @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
      setT (analytic_representative_value f).
Proof.
move=>hXi.
have hLinear:=@norm_bounded_linear_analytic R X R^o NX (fun r=>`|r|) hNX
  (@scalar_absolute_value_norm R) setT (fun x _=>norm_full_domain_interior NX x) xi hXi.
have hPower:=@norm_analytic_scalar_power R X NX hNX setT xi k hLinear.
have [f hValues]:=@analytic_representative_from_domain R X NX hNX 0 setT (fun x=>(xi x)^+k) (hPower 0 Logic.I).
exists f;split;first exact:hValues.
by rewrite hValues.
Qed.

(** Source for [weierstrass_functional_power_coefficients]:
    the original monic dividend has exactly one nonzero
    mixed coefficient, at (k,0), supporting preparation
    in 3.4.6(2), pp. 322–324. All coefficients
    are read from actual derivatives on exact lines. *)
Theorem weierstrass_functional_power_coefficients (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (f:analytic_representative_type hNX (0:X)) (q:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  analytic_representative_value f=(fun x=>(xi x)^+k) ->
  @norm_analytic R X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
    setT (analytic_representative_value f) ->
  (forall i j,is_weierstrass_split_coefficient (analytic_germ f) v inclusion i j (q i j)) ->
  forall i j z,q i j z=if ((i==k)&&(j==0))%N then 1 else 0.
Proof.
move=>hSplit hValues hf hQ i j z.
pose N:=fun r:R^o=>`|r|.
pose hN:=@scalar_absolute_value_norm R.
pose F:=analytic_representative_value f.
have [C [P [hC hP]]]:=@analytic_iterated_directional_coefficients_exist R X R^o NX N hNX hN
  setT F v (inclusion z) hf.
have hOriginal:=@weierstrass_iterated_germ_coefficient R X K NX hNX (analytic_germ f) f setT
  v inclusion i j (q i j) (C i) (P i j) z (erefl _) Logic.I hf (hQ i j) (hC i).1 (hP i j).1.
have hFirst z':C i (inclusion z')=if (i==k)%N then 1 else 0.
  have hLine t (ht:`|t|<1):F (inclusion z'+t*:v)=
      \sum_(n<k.+1) t^+n*(if ((n:nat)==k)%N then (1:R) else 0).
    rewrite /F hValues addrC (weierstrass_line_functional_coordinate hSplit).
    rewrite (bigD1 (Ordinal (ltnSn k))) //= eqxx mulr1.
    have hOthers:(\sum_(n<k.+1 | n!=Ordinal (ltnSn k))
      t^+n*(if ((n:nat)==k)%N then (1:R) else 0))=0.
      apply:big1=>n hn.
      have hNe:((n:nat)!=k)%N by move:hn;rewrite -val_eqE /=.
      by rewrite (negbTE hNe) mulr0.
    by rewrite hOthers addr0.
  have hFinite:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN
    setT F i v (inclusion z') (C i) k.+1 (fun n=>if (n==k)%N then 1 else 0) 1
    Logic.I hf (hC i).1 ltr01 hLine.
  case hSmall:(i<k.+1)%N in hFinite *=>//.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnSn in hSmall.
  by rewrite (negbTE hNe).
have hLine t (ht:`|t|<1):C i (0+t*:inclusion z)=
    \sum_(n<1) t^+n*(if (i==k)%N then (1:R) else 0).
  rewrite add0r -linearZ /= hFirst big_ord1 /= expr0 mul1r.
  reflexivity.
have hSecond:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN
  setT (C i) j (inclusion z) 0 (P i j) 1 (fun _=>if (i==k)%N then 1 else 0) 1
  Logic.I (hC i).2 (hP i j).1 ltr01 hLine.
rewrite hOriginal hSecond.
clear - R i k;case:j=>[|j];by rewrite ?ltn0 ?ltnS ?leqn0 /= ?andbT ?andbF.
Qed.
