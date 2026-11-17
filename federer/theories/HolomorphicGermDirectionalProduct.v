(** Federer (1969), 3.4.12, p. 339, extending the
    Taylor argument of 3.4.8(5), p. 328: actual complex
    germ coefficients satisfy the finite product convolution.
    Reuse the proved original complex Leibniz coefficient theorem
    on a common actual holomorphic neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  NormAnalyticUP NormAnalyticComplexProduct AnalyticDirectionalCoefficient AnalyticComplexDirectionalCoefficientProduct
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermSealed HolomorphicGermOperationsUP
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermRingLaws
  HolomorphicGermDirectionalCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Product.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [holomorphic_germ_directional_coefficient_product]:
    the actual divided product coefficient is the convolution
    of the two original divided coefficient families, extending
    3.1.11, p. 222, under 3.4.12, p. 339. *)
Theorem holomorphic_germ_directional_coefficient_product a k
    (alpha beta:[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR a)]) v:
  @holomorphic_germ_directional_coefficient R X NX hNX a k (alpha*beta) v=
    \sum_(j<k.+1) (@holomorphic_germ_directional_coefficient R X NX hNX a (k-j)%N alpha v)*
      (@holomorphic_germ_directional_coefficient R X NX hNX a j beta v).
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNXR a alpha.
have [g hg]:=@holomorphic_germ_has_representative R X NX hNXR a beta.
have [U [ha [hF hG]]]:=@holomorphic_representatives_common_domain R X NX hNXR a f g.
pose F:=holomorphic_representative_value f.
pose G:=holomorphic_representative_value g.
have hFG:=norm_analytic_complex_product hF.1 hG.1.
have hEachF i:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U F i v hF.1.
have hEachG i:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN U G i v hG.1.
have [D hD]:=choice hEachF.
have [E hE]:=choice hEachG.
have [H [hH _]]:=@analytic_directional_coefficient_exists R XR CR NX N hNXR hN
  U (fun x=>F x*G x) k v hFG.
have hConvolution:=@analytic_complex_directional_coefficient_product R XR NX hNXR U F G k v a D E H
  ha hF.1 hG.1 (fun i _=>(hD i).1) (fun i _=>(hE i).1) hH.
pose p:=@holomorphic_multiply_representatives R X NX hNXR a f g.
have hRep:holomorphic_germ p=(alpha*beta:@holomorphic_germ_ring R X NX hNXR a).
  rewrite -hf -hg.
  exact:esym (@holomorphic_germ_multiply_equation R X NX hNXR a _ _ _
    (@HolomorphicGerms.laws R X NX hNXR a) f g).
have hValue:=@holomorphic_directional_coefficient_at_germ_centre R X NX hNX a k
  (alpha*beta) p U v H hRep ha hFG hH.
rewrite -hValue hConvolution.
apply:eq_bigr=>j _.
rewrite (@holomorphic_directional_coefficient_at_germ_centre R X NX hNX a (k-j)%N
  alpha f U v (D (k-j)%N) hf ha hF.1 (hD _).1).
rewrite (@holomorphic_directional_coefficient_at_germ_centre R X NX hNX a j
  beta g U v (E j) hg ha hG.1 (hE _).1).
reflexivity.
Qed.
End Product.
