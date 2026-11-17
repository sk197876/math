(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    the original derivative-inverse germ relation
    holds for the actual analytic functions
    throughout their connected common cylinder.
    Reuse analytic germ arithmetic and the
    existing identity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric NormAnalyticUP NormAnalyticOperations NormAnalyticComplexProduct
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing
  HolomorphicGermConnectedAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_product_identity]:
    W'_(m+1)t_(m+1)-delta=s_(m+1)W_(m+1)
    on the actual domain, 3.4.12, p. 339, extending 3.4.8(10),
    p. 331. The identity is proved
    from the original germ relation and
    analyticity on the connected domain. *)
Theorem holomorphic_germ_product_identity (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) (A:set X)
    (f g d s w:@holomorphic_representative_type R X NX hNX a):
  @open (real_norm_metric_space hNX) A ->A a ->
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (holomorphic_representative_value f) ->
  @norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (holomorphic_representative_value g) ->
  @norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (holomorphic_representative_value d) ->
  @norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (holomorphic_representative_value s) ->
  @norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (holomorphic_representative_value w) ->
  (holomorphic_germ f:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])*(holomorphic_germ g:@holomorphic_germ_ring R X NX hNX a)-(holomorphic_germ d:@holomorphic_germ_ring R X NX hNX a) =
    (holomorphic_germ s:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])*(holomorphic_germ w:@holomorphic_germ_ring R X NX hNX a) ->
  forall x,A x ->holomorphic_representative_value f x*holomorphic_representative_value g x-
    holomorphic_representative_value d x = holomorphic_representative_value s x*holomorphic_representative_value w x.
Proof.
move=>hOpen ha hConnected hf hg hd hs hw hEquation.
pose product:=@holomorphic_multiply_representatives R X NX hNX a f g.
pose negative:=@holomorphic_negate_representative R X NX hNX a d.
pose left:=@holomorphic_add_representatives R X NX hNX a product negative.
pose right:=@holomorphic_multiply_representatives R X NX hNX a s w.
have hLeft:@norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
    A (holomorphic_representative_value left).
  exact:(norm_analytic_subtract (norm_analytic_complex_product hf hg) hd).
have hRight:@norm_analytic R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
    A (holomorphic_representative_value right).
  exact:norm_analytic_complex_product hs hw.
have hGerms:holomorphic_germ left=holomorphic_germ right.
  rewrite /left /right /product /negative
    -!(holomorphic_germ_add_equation (@HolomorphicGerms.laws R X NX hNX a))
    -!(holomorphic_germ_multiply_equation (@HolomorphicGerms.laws R X NX hNX a))
    -(holomorphic_germ_negate_equation (@HolomorphicGerms.laws R X NX hNX a)).
  exact:hEquation.
exact:(@holomorphic_germ_connected_agreement R X NX hNX a A left right
  hOpen ha hConnected hLeft hRight hGerms).
Qed.
