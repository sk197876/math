(** Federer (1969), 3.4.6, p. 323: analytic
    realisation of the finite total-degree grouping retains
    every original mixed divided coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm AnalyticGermUP AnalyticGermJetsSealed
  WeierstrassCoefficientUP WeierstrassGroupedUP WeierstrassTransverseUP WeierstrassTransverseLaws
  WeierstrassSplitFormExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_grouped_original_coefficients]:
    the grouped germ has exactly the original double
    sequence, proving the coefficient correspondence used in
    3.4.6, p. 323. Exact line coordinates
    and finite polynomial uniqueness identify each coefficient;
    no derivative-series interchange is assumed. *)
Theorem weierstrass_grouped_original_coefficients (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (q:nat->nat->K->R) (alpha:analytic_germ_space hNX (0:X)):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  is_weierstrass_grouped_germ xi projection q alpha ->
  forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (q i j).
Proof.
move=>hSplit hGrouped i j F hF z.
have hPolynomial x:(\sum_(s<(i+j).+1) (xi x)^+s*q s (i+j-s)%N (projection x))=
    sform_polynomial_value F x.
  rewrite (hGrouped (i+j)%N x) sform_polynomial_diagonal_value hF.
  change ((((i+j)`!)%:R:R)^-1*@ContinuousMultilinear.evaluation R (i+j)%N X R^o NX
    (fun r=>`|r|) hNX (@scalar_absolute_value_norm R) [ffun _:'I_(i+j)=>x]
    (@AnalyticGermJets.value R X NX hNX 0 (i+j)%N alpha)=
    (((i+j)`!)%:R:R)^-1*@ContinuousMultilinear.evaluation R (i+j)%N X R^o NX
    (fun r=>`|r|) hNX (@scalar_absolute_value_norm R) [ffun s=>tnth [tuple x | _<(i+j)%N] s]
    (@AnalyticGermJets.value R X NX hNX 0 (i+j)%N alpha)).
  have hTuple:[ffun _: 'I_(i+j)=>x]=[ffun s=>tnth [tuple x | _<(i+j)%N] s].
    by apply/ffunP=>s;rewrite !ffunE tnth_mktuple.
  by rewrite hTuple.
have hValues (t:R):sform_polynomial_value F (t*:v+inclusion z)=
    \sum_(s<(i+j).+1) t^+s*q s (i+j-s)%N z.
  rewrite -(hPolynomial (t*:v+inclusion z)).
  apply:eq_bigr=>s _.
  by rewrite (weierstrass_line_functional_coordinate hSplit)
    (weierstrass_line_transverse_coordinate hSplit).
have hi:(i<=i+j)%N by rewrite leq_addr.
have hCoefficient:=@weierstrass_split_form_coefficient_unique R X (i+j)%N F v (inclusion z)
  (fun s=>q s (i+j-s)%N z) hValues i hi.
have hDegree:(i+j-i)%N=j by rewrite addnC addnK.
by rewrite hDegree in hCoefficient.
Qed.
