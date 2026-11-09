(** Federer (1969), 3.4.6, pp. 323–324: the
    finite transverse remainder has exactly the low rows
    of the original actual mixed coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal
  NormTaylorLineValues AnalyticGermRepresentatives AnalyticGermUP AnalyticDirectionalCoefficient
  AnalyticDirectionalPolynomialLine WeierstrassCoefficientUP WeierstrassIteratedGermCoefficient
  WeierstrassTransverseUP WeierstrassFiniteRemainderLine WeierstrassLineCoefficientAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_finite_remainder_coefficients]:
    the low rows agree with the original remainder
    and every high row vanishes, 3.4.6,
    pp. 323–324. All coefficients are actual derivatives
    of actual analytic representatives; no formal-series
    identification or coefficient transport is assumed. *)
Theorem weierstrass_finite_remainder_coefficients (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K) k
    (alpha beta:analytic_germ_space hNX (0:X))
    (f g:analytic_representative_type hNX (0:X)) (U A:set X)
    (C:nat->X->R) (r s:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  analytic_germ f=alpha ->analytic_germ g=beta ->U 0 ->A 0 ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    U (analytic_representative_value f) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value g) ->
  (forall i,@is_analytic_directional_coefficient R X R^o NX (fun t=>`|t|)
    hNX (@scalar_absolute_value_norm R) U (analytic_representative_value f) i v (C i) /\
    @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) U (C i)) ->
  (forall x,analytic_representative_value g x=\sum_(i<k) (xi x)^+i*C i (inclusion (projection x))) ->
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (r i j)) ->
  (forall i j,is_weierstrass_split_coefficient beta v inclusion i j (s i j)) ->
  forall i j z,s i j z=if (i<k)%N then r i j z else 0.
Proof.
move=>hSplit hRepF hRepG haU haA hf hg hC hValues hR hS i j z.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose F:=analytic_representative_value f.
pose G:=analytic_representative_value g.
have [D [hD hAnalyticD]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN A G i v hg.
have [P [hP hAnalyticP]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN A D j (inclusion z) hAnalyticD.
have hOriginal:=@weierstrass_iterated_germ_coefficient R X K NX hNX beta g A v inclusion
  i j (s i j) D P z hRepG haA hg (hS i j) hD hP.
have hTransverse z' (ha:A (inclusion z')):
    D (inclusion z')=if (i<k)%N then C i (inclusion z') else 0.
  apply:(@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN A G
    i v (inclusion z') D k (fun n=>C n (inclusion z')) 1 ha hg hD ltr01)=>t _.
  rewrite /G hValues (@weierstrass_finite_remainder_transverse_line R X K NX NK v xi inclusion projection k C hSplit).
  reflexivity.
have hOpen:norm_domain_interior NX A 0:=
  ((norm_analytic_class_all_orders hg 0%N).1 0 haA).1.
have [rho [hRho hBall]]:=hOpen.
have [delta [hDelta hSmall]]:=@norm_scalar_line_small_increments R X NX hNX (inclusion z) rho hRho.
have hLine t (ht:`|t|<delta):
    D (0+t*:inclusion z)=if (i<k)%N then C i (0+t*:inclusion z) else 0.
  have ha:A (inclusion (t*:z)).
    rewrite linearZ /=;have hh:=hBall (t*:inclusion z) (hSmall t ht).
    by rewrite add0r in hh.
  have hh:=hTransverse (t*:z) ha.
  rewrite linearZ /= in hh.
  rewrite add0r;exact:hh.
rewrite hOriginal.
case hi:(i<k)%N.
- have [E [hE hAnalyticE]]:=@analytic_directional_coefficient_exists R X R^o NX N hNX hN U (C i) j (inclusion z) (hC i).2.
  have hInput:=@weierstrass_iterated_germ_coefficient R X K NX hNX alpha f U v inclusion
    i j (r i j) (C i) E z hRepF haU hf (hR i j) (hC i).1 hE.
  rewrite hInput.
  apply:(@weierstrass_line_coefficients_agree R X X NX NX hNX hNX A U D (C i) j
    (inclusion z) (inclusion z) 0 0 P E haA haU hAnalyticD (hC i).2 hP hE).
  exists delta;split;first exact:hDelta.
  move=>t ht;by rewrite (hLine t ht) hi.
- have hFinite:=@analytic_directional_polynomial_line_coefficient R X R^o NX N hNX hN A D
    j (inclusion z) 0 P 0%N (fun _=>0) delta haA hAnalyticD hP hDelta.
  have hExact t (ht:`|t|<delta):D (0+t*:inclusion z)=\sum_(n<0) t^+n*:(0:R^o).
    by rewrite (hLine t ht) hi big_ord0.
  have hh:=hFinite hExact.
  by rewrite ltn0 in hh.
Qed.
