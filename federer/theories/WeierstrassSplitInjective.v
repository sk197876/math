(** Federer (1969), 3.4.6, p. 323: the original
    complete mixed-coefficient sequence determines an analytic
    germ uniquely. The proof uses actual Taylor injectivity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialTaylorTerms HomogeneousPolynomialFunctions
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermJetsSealed
  AnalyticGermCoefficientForms AnalyticGermTaylorInjective WeierstrassCoefficientUP
  WeierstrassTransverseUP WeierstrassSplitFormExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficients_injective]:
    original double sequences represent members of the
    actual analytic germ ring uniquely, 3.4.6, p. 323.
    The transverse splitting reconstructs each homogeneous
    Taylor polynomial; polarization and actual Taylor
    injectivity then identify the germs. *)
Theorem weierstrass_split_coefficients_injective (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (alpha beta:analytic_germ_space hNX (0:X)) (C D:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (C i j)) ->
  (forall i j,is_weierstrass_split_coefficient beta v inclusion i j (D i j)) ->
  (forall i j z,C i j z=D i j z) ->alpha=beta.
Proof.
move=>hSplit hC hD hEqual.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
have [G [hG _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 beta.
have hCoefficient i j z:
    sform_polynomial_value (symmetric_taylor_term j (F (i+j)%N) v) (inclusion z)=
    sform_polynomial_value (symmetric_taylor_term j (G (i+j)%N) v) (inclusion z).
  by rewrite -(hC i j (F (i+j)%N) (hF (i+j)%N) z)
    -(hD i j (G (i+j)%N) (hG (i+j)%N) z) hEqual.
have hForms m:F m=G m.
  apply:(@sform_polynomial_injective R X R^o m (@pchar_num R));apply:funext=>x.
  have hDecompose:x=(xi x)*:v+inclusion (projection x).
    by rewrite (weierstrass_transverse_projection_equation hSplit) addrC subrK.
  rewrite hDecompose !weierstrass_split_form_line_expansion.
  apply:eq_bigr=>i _.
  have hi:(i<=m)%N by have:=ltn_ord i;rewrite ltnS.
  have hSame:=hCoefficient i (m-i)%N (projection x).
  rewrite (subnKC hi) in hSame.
  by rewrite hSame.
apply:(@analytic_germ_jets_injective R X NX hNX 0 alpha beta)=>m.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R m X R^o NX
  (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)))=>u.
have hTuple:[ffun s=>tnth [tuple u j | j<m] s]=u.
  by apply/ffunP=>s;rewrite ffunE tnth_mktuple.
have hFirst:=hF m [tuple u j | j<m].
have hSecond:=hG m [tuple u j | j<m].
rewrite hTuple hForms in hFirst;rewrite hTuple in hSecond.
exact:etrans (esym hFirst) hSecond.
Qed.
