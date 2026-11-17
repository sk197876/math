(** Federer (1969), 3.4.12, p. 339: the original complex
    mixed coefficients satisfy the two-index product convolution.
    Reuse actual iterated directional fields and the proved
    complex Leibniz adapter; no formal product rule is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm NormAnalyticUP NormAnalyticComplexProduct
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP
  HolomorphicGermOperationsUP HolomorphicGermSealed HolomorphicGermRingLaws
  AnalyticIteratedDirectionalCoefficients AnalyticComplexIteratedCoefficientProduct
  ComplexWeierstrassCoefficientUP ComplexWeierstrassIteratedGermCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Products.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).

(** Source for [complex_weierstrass_split_coefficient_product]: the
    literal original rectangular convolution in the complex extension
    of 3.4.6, p. 323, required by 3.4.12, p. 339. *)
Theorem complex_weierstrass_split_coefficient_product
    (alpha beta:holomorphic_germ_space hNXR (0:X)) (v:X) (inclusion:Hom K X)
    (A B T:nat->nat->K->C):
  (forall i j,is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (A i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX beta v inclusion i j (B i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX
    (@HolomorphicGerms.mul R X NX hNXR 0 alpha beta) v inclusion i j (T i j)) ->
  forall i j z,T i j z=\sum_(r<i.+1) \sum_(s<j.+1) A (i-r)%N (j-s)%N z*B r s z.
Proof.
move=>hA hB hT i j z.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNXR 0 alpha.
have [g hg]:=@holomorphic_germ_has_representative R X NX hNXR 0 beta.
have [U [ha [hF hG]]]:=@holomorphic_representatives_common_domain R X NX hNXR 0 f g.
pose F:=holomorphic_representative_value f.
pose G:=holomorphic_representative_value g.
have hFG:=norm_analytic_complex_product hF.1 hG.1.
have [D [P [hD hP]]]:=@analytic_iterated_directional_coefficients_exist R XR CR NX N hNXR hN
  U F v (inclusion z) hF.1.
have [E [Q [hE hQ]]]:=@analytic_iterated_directional_coefficients_exist R XR CR NX N hNXR hN
  U G v (inclusion z) hG.1.
have [H [S [hH hS]]]:=@analytic_iterated_directional_coefficients_exist R XR CR NX N hNXR hN
  U (fun x=>F x*G x) v (inclusion z) hFG.
pose gamma:=@HolomorphicGerms.mul R X NX hNXR 0 alpha beta.
pose p:=@holomorphic_multiply_representatives R X NX hNXR 0 f g.
have hRep:holomorphic_germ p=gamma.
  by rewrite /gamma -hf -hg (@holomorphic_germ_multiply_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNXR 0)).
have hOriginal:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX gamma p U
  v inclusion i j (T i j) (H i) (S i j) z hRep ha hFG (hT i j) (hH i).1 (hS i j).1.
have hConvolution:=@analytic_complex_iterated_coefficient_product R XR NX hNXR U F G
  v (inclusion z) 0 D E P Q i j (H i) (S i j) ha hF.1 hG.1
  (fun r=>(hD r).1) (fun r=>(hE r).1) (fun r s=>(hP r s).1) (fun r s=>(hQ r s).1)
  (hH i).1 (hS i j).1.
rewrite hOriginal hConvolution;apply:eq_bigr=>r _;apply:eq_bigr=>s _.
have hFirst:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX alpha f U
  v inclusion (i-r)%N (j-s)%N (A (i-r)%N (j-s)%N) (D (i-r)%N) (P (i-r)%N (j-s)%N) z
  hf ha hF.1 (hA _ _) (hD _).1 (hP _ _).1.
have hSecond:=@complex_weierstrass_iterated_germ_coefficient R X K NX hNX beta g U
  v inclusion r s (B r s) (E r) (Q r s) z hg ha hG.1 (hB r s) (hE r).1 (hQ r s).1.
by rewrite -hFirst -hSecond.
Qed.
End Products.
