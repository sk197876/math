(** Federer (1969), 3.4.12, p. 339: the original finite
    complex transverse remainder retains exactly the low mixed
    coefficient rows. Reuse actual real line Taylor comparisons
    for the same complex-valued functions and original directions. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormDifferentialUP NormRegularity NormAnalyticUP NormAnalyticLocal
  NormTaylorLineValues HolomorphicGermRepresentatives HolomorphicGermUP AnalyticDirectionalCoefficient
  AnalyticDirectionalPolynomialLine ComplexWeierstrassCoefficientUP ComplexWeierstrassIteratedGermCoefficient
  ComplexWeierstrassTransverseUP ComplexWeierstrassRealRemainderLine NormWeierstrassLineCoefficientAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_finite_remainder_coefficients]: the
    actual low rows agree and all high rows vanish, extending
    3.4.6, pp. 323–324, under 3.4.12, p. 339. Every
    coefficient is an actual derivative of its original representative. *)
Theorem complex_weierstrass_finite_remainder_coefficients v (xi:Hom X C^o)
    (inclusion:Hom K X) (projection:Hom X K) k
    (alpha beta:holomorphic_germ_space hNXR (0:X))
    (f g:@holomorphic_representative_type R X NX hNXR 0) (U A:set X)
    (D:nat->X->C) (r s:nat->nat->K->C):
  is_complex_weierstrass_transverse_space NX NK v xi inclusion projection ->
  holomorphic_germ f=alpha ->holomorphic_germ g=beta ->U 0 ->A 0 ->
  @norm_analytic R XR CR NX N hNXR hN U (holomorphic_representative_value f) ->
  @norm_analytic R XR CR NX N hNXR hN A (holomorphic_representative_value g) ->
  (forall i,@is_analytic_directional_coefficient R XR CR NX N hNXR hN
    U (holomorphic_representative_value f) i v (D i) /\
    @norm_analytic R XR CR NX N hNXR hN U (D i)) ->
  (forall x,holomorphic_representative_value g x=\sum_(i<k) (xi x)^+i*D i (inclusion (projection x))) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (r i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX beta v inclusion i j (s i j)) ->
  forall i j z,s i j z=if (i<k)%N then r i j z else 0.
Proof.
move=>hSplit hRepF hRepG haU haA hf hg hD hValues hR hS i j z.
pose F:=holomorphic_representative_value f.
pose G:=holomorphic_representative_value g.
have [E [hE hAnalyticE]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN A G i v hg.
have [P [hP hAnalyticP]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN
  A E j (inclusion z) hAnalyticE.
have hOriginal:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX beta g A v inclusion
  i j (s i j) E P z hRepG haA hg (hS i j) hE hP.
have hTransverse z' (ha:A (inclusion z')):
    E (inclusion z')=if (i<k)%N then D i (inclusion z') else 0.
  apply:(@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN A G
    i v (inclusion z') E k (fun n=>D n (inclusion z')) 1 ha hg hE ltr01)=>t _.
  rewrite /G hValues.
  exact:(@complex_weierstrass_real_transverse_line R X K NX NK v xi inclusion projection k D hSplit z' t).
have hOpen:@norm_domain_interior R XR NX A 0:=
  ((norm_analytic_class_all_orders hg 0%N).1 0 haA).1.
have [rho [hRho hBall]]:=hOpen.
have [delta [hDelta hSmall]]:=@norm_scalar_line_small_increments R XR NX hNXR (inclusion z) rho hRho.
have hLine (t:R) (ht:`|t|<delta):
    E ((0:XR)+t*:(inclusion z:XR))=if (i<k)%N then D i ((0:XR)+t*:(inclusion z:XR)) else 0.
  have hLinear:inclusion (ComplexScalars.embed R t*:z)=(t*:(inclusion z:XR):XR).
    by rewrite linearZ.
  have ha:A (inclusion (ComplexScalars.embed R t*:z)).
    rewrite hLinear;have hh:=hBall (t*:(inclusion z:XR)) (hSmall t ht).
    by rewrite add0r in hh.
  have hh:=hTransverse (ComplexScalars.embed R t*:z) ha.
  rewrite hLinear in hh;rewrite add0r;exact:hh.
rewrite hOriginal.
case hi:(i<k)%N.
- have [H [hH hAnalyticH]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN
    U (D i) j (inclusion z) (hD i).2.
  have hInput:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX alpha f U v inclusion
    i j (r i j) (D i) H z hRepF haU hf (hR i j) (hD i).1 hH.
  rewrite hInput.
  apply:(@norm_weierstrass_line_coefficients_agree R XR XR CR N hN NX NX hNXR hNXR
    A U E (D i) j (inclusion z) (inclusion z) 0 0 P H haA haU hAnalyticE (hD i).2 hP hH).
  exists delta;split;first exact:hDelta.
  move=>t ht;by rewrite (hLine t ht) hi.
- have hFinite:=@analytic_directional_polynomial_line_coefficient R XR CR NX N hNXR hN A E
    j (inclusion z) 0 P 0%N (fun _=>0) delta haA hAnalyticE hP hDelta.
  have hExact (t:R) (ht:`|t|<delta):E ((0:XR)+t*:(inclusion z:XR))=\sum_(n<0) t^+n*:(0:CR).
    by rewrite (hLine t ht) hi big_ord0.
  have hh:=hFinite hExact;by rewrite ltn0 in hh.
Qed.
End Coefficients.
