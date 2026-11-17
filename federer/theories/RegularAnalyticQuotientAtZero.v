(** Federer (1969), 3.4.8(8), p. 329:
    the finite quotient uses the original
    coefficient germs at zero. Identify the
    proved equal centres P(0) and zero
    through the existing representative interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives WeierstrassTransverseUP WeierstrassTransversePullback WeierstrassRegularUP
  CommutativeIdealUP CommutativeSubringUP CommutativeQuotientUP
  CommutativePolynomialSealed CommutativePolynomialEvaluationSealed
  RingScalarRestriction RingSubmoduleUP FiniteModuleSurjectiveScalars GeneratedRingSurjectiveScalars
  PointedAnalyticPullbackUP PointedAnalyticPullbackComposition OrdinaryPointedAnalyticPullback
  EqualAnalyticGermCentres RegularAnalyticQuotientFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Quotient.
Variable R:realType.
Variables X K:lmodType R.
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Variable v:X.
Variable xi:Hom X R^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Hypothesis hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Hypothesis hXiValues:forall x,analytic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A0:=[the comNzRingType of (@analytic_germ_ring R K NK hNK 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation pullback:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).
Variable C:comNzRingType.
Variable I:set G.
Variable pi:{rmorphism G->C}.
Hypothesis hIdeal:is_commutative_ideal I.
Hypothesis hQuotient:is_commutative_ideal_quotient I pi.

(** Source for [regular_analytic_quotient_original_centre]:
    the original coefficient ring is O_0(K),
    and the quotient is finite and generated
    by its original coordinate class, 3.4.8(8),
    p. 329. The auxiliary centre identification
    preserves all original representatives and is
    a local existence witness. *)
Theorem regular_analytic_quotient_original_centre (Phi:G) k:
  I Phi ->is_weierstrass_regular_germ Phi k v ->
  exists E0:{rmorphism A0->G},is_pointed_analytic_germ_pullback projection E0 /\
    is_finitely_generated_ring_submodule
      (setT:set [the lmodType A0 of ring_restricted_space
        (GRing.RMorphism.clone A0 C (pi \o E0) _) C^o]) /\
    is_generated_commutative_subring
      (fun y:C=>y = pi Gamma \/exists a:A0,y = pi (E0 a)) setT.
Proof.
move=>hPhi hRegular.
pose B:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hB:=CommutativePolynomial.laws A.
pose J:=@CommutativePolynomialEvaluation.map A B G embed variable coefficient hB pullback Gamma.
have hJ:=@CommutativePolynomialEvaluation.laws A B G embed variable coefficient hB pullback Gamma.
have [hFinite [hGenerated _]]:=@regular_analytic_quotient_finite_extension R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embed variable coefficient hB J hJ
  C I pi hIdeal hQuotient Phi k hPhi hRegular.
have [F [H [hF [hH [hFH hHF]]]]]:=@equal_analytic_germ_centres_ring_witnesses R K NK hNK
  0 (projection 0) (esym (linear0 projection)).
pose E0:{rmorphism A0->G}:=GRing.RMorphism.clone A0 G (pullback \o F) _.
have hOrdinary:=@ordinary_analytic_ring_pullback_pointed_laws R X K NX NK hNX hNK setT projection 0
  (@weierstrass_transverse_projection_analytic R X K NX NK hNX hNK v xi inclusion projection hSplit).
have hE0:is_pointed_analytic_germ_pullback projection E0.
  exact:(pointed_analytic_pullback_composes hOrdinary hF).
have hOnto:forall b:A,exists a:A0,F a = b by move=>b;exists (H b);exact:hHF b.
pose scalar:{rmorphism A->C}:=GRing.RMorphism.clone A C (pi \o pullback) _.
pose scalar0:{rmorphism A0->C}:=GRing.RMorphism.clone A0 C (pi \o E0) _.
have hTriangle a:scalar (F a) = scalar0 a by [].
exists E0;split;first exact:hE0.
split.
- exact:(@finite_module_surjective_scalar_restriction A0 A C scalar0 F scalar hTriangle hOnto hFinite).
- exact:(@generated_ring_surjective_coefficients A0 A C scalar0 F scalar (pi Gamma) hTriangle hOnto hGenerated).
Qed.
End Quotient.
