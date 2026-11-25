(** Federer (1969), 3.4.12, p. 339: the actual square
    map has a local holomorphic inverse at every nonzero point.
    Reuse the existing product differential and finite inverse theorem;
    an inverse or nonzero Jacobian is not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import InnerNorm TensorUP Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexModulus ComplexScalarNorm ComplexScalarHermitian ComplexCoefficientAlgebra HermitianRealImaginary
  LinearBasis FiniteBasisCriterion NormDifferentialUP NormDifferentialLinear NormOpenDomainLaws
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra NormDiffeomorphismUP
  HolomorphicUP ComplexSquareCoverObstruction FiniteHolomorphicInverseNormIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Inverse.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_square_nonzero_local_inverse]: the
    local complex branches needed in the covering qualification of
    3.4.12, p. 339. The derivative is the actual map
    h mapped to 2zh; both inverse identities are conclusions. *)
Theorem complex_square_nonzero_local_inverse (a:C):a<>0 ->
  exists r:R,0<r /\exists g:C->C,
    @is_norm_diffeomorphism R CR CR N N hN hN
      [set x|N (x-a)<r] ((fun z:C=>z^+2) @` [set x|N (x-a)<r])
      (fun z:C=>z^+2) g 1%N /\
    @is_holomorphic R C^o C^o N N hN hN
      ((fun z:C=>z^+2) @` [set x|N (x-a)<r]) g.
Proof.
move=>hA.
pose Id:Hom CR CR:=hom_of_linear (linear_id CR).
have hIdBound:@norm_bounded_linear R CR CR N N Id.
  exists 1;split;first exact:ler01.
  by move=>z;rewrite /Id hom_of_linearE mul1r.
have hId:=@norm_differential_linear R CR CR N N hN hN setT a Id
  (@norm_full_domain_interior R CR N a) hIdBound.
have hBound (z w:CR):N (complex_real_multiply z w)<=1*(N z*N w).
  by rewrite mul1r /complex_real_multiply complex_modulus_mul.
pose L:=norm_bilinear_product_linear_term (@complex_real_multiply_bilinear R) a a Id Id.
have hD:=@norm_differential_bilinear_product R CR CR CR CR N N N N
  hN hN hN hN (@complex_real_multiply R) (@complex_real_multiply_bilinear R)
  1 setT Id Id a Id Id ler01 hBound hId hId.
have hSquare:(fun z:CR=>complex_real_multiply (Id z) (Id z))=(fun z:CR=>z^+2).
  apply:funext=>z;by rewrite /Id hom_of_linearE /complex_real_multiply expr2.
rewrite hSquare in hD.
have hValue z:L z=(2*a)*z.
  change (z*a+a*z=(2*a)*z);ring.
have hTwo:(2:C)!=0.
  rewrite -(@rmorph_nat R C (ComplexScalars.embed R) 2) fmorph_eq0.
  by rewrite pnatr_eq0.
have hProduct:(2*a:C)!=0 by rewrite mulf_eq0 negb_or hTwo;apply/eqP.
have hInjective:injective L.
  move=>x y hEqual.
  have hStep:(2*a)*x=(2*a)*y:=eq_trans (esym (hValue x)) (eq_trans hEqual (hValue y)).
  have hBack:=congr1 (fun z:C=>(2*a)^-1*z) hStep.
  by rewrite [LHS]mulrA [RHS]mulrA (mulVf hProduct) !mul1r in hBack.
pose e (i:'I_1):C^o:=1.
have he:is_basis e.
  apply:finite_basis_criterion.
  - move=>c hc i;rewrite /e big_ord1 in hc;rewrite ord1.
    change (c ord0*1=0) in hc;by rewrite mulr1 in hc.
  - move=>x;exists (fun _=>x);by rewrite big_ord1 /e;change (x=x*1);rewrite mulr1.
pose B:=hermitian_real_part (@complex_scalar_hermitian R).
pose hB:=hermitian_real_inner_product (@complex_scalar_hermitian_laws R).
have hNorm:N=inner_norm hB by apply:funext=>z;exact:esym (complex_scalar_inner_norm z).
have [r [hR [hInside [g [hInverse [hForward hBackward]]]]]]:=
  @finite_holomorphic_inverse_identified_inner_norm R C^o B hB N hN 1 e he setT
    (fun z:C=>z^+2) a L hNorm (@complex_square_map_holomorphic R) Logic.I hD hInjective.
by exists r;split;last exists g.
Qed.
End Inverse.
