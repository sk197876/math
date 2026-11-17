(** Federer (1969), 3.4.8(10), p. 331:
    the original derivative-inverse germ relation
    holds for the actual analytic functions
    throughout their connected common cylinder.
    Reuse analytic germ arithmetic and the
    existing identity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP NormAnalyticOperations NormAnalyticScalarProducts
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  AnalyticGermConnectedAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_product_identity]:
    W'_(m+1)t_(m+1)-delta=s_(m+1)W_(m+1)
    on the actual domain, 3.4.8(10),
    p. 331. The identity is proved
    from the original germ relation and
    analyticity on the connected domain. *)
Theorem analytic_germ_product_identity (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (A:set X)
    (f g d s w:@analytic_representative_type R X NX hNX a):
  @open (real_norm_metric_space hNX) A ->A a ->
  @connected (real_norm_metric_space hNX) A ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value f) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value g) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value d) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value s) ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A (analytic_representative_value w) ->
  (analytic_germ f:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])*(analytic_germ g:@analytic_germ_ring R X NX hNX a)-(analytic_germ d:@analytic_germ_ring R X NX hNX a) =
    (analytic_germ s:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)])*(analytic_germ w:@analytic_germ_ring R X NX hNX a) ->
  forall x,A x ->analytic_representative_value f x*analytic_representative_value g x-
    analytic_representative_value d x = analytic_representative_value s x*analytic_representative_value w x.
Proof.
move=>hOpen ha hConnected hf hg hd hs hw hEquation.
pose product:=@analytic_multiply_representatives R X NX hNX a f g.
pose negative:=@analytic_negate_representative R X NX hNX a d.
pose left:=@analytic_add_representatives R X NX hNX a product negative.
pose right:=@analytic_multiply_representatives R X NX hNX a s w.
have hLeft:@norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value left).
  exact:(norm_analytic_subtract (norm_analytic_scalar_product hf hg) hd).
have hRight:@norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    A (analytic_representative_value right).
  exact:norm_analytic_scalar_product hs hw.
have hGerms:analytic_germ left=analytic_germ right.
  rewrite /left /right /product /negative
    -!(analytic_germ_add_equation (@AnalyticGerms.laws R X NX hNX a))
    -!(analytic_germ_multiply_equation (@AnalyticGerms.laws R X NX hNX a))
    -(analytic_germ_negate_equation (@AnalyticGerms.laws R X NX hNX a)).
  exact:hEquation.
exact:(@analytic_germ_connected_agreement R X NX hNX a A left right
  hOpen ha hConnected hLeft hRight hGerms).
Qed.
