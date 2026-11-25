(** Federer (1969), 3.4.5, p. 321: analytic
    coefficient germs cannot have all-order one-sided flat
    decay unless they are zero. The proof uses actual
    Taylor jets and the identity consequence of 3.1.24,
    p. 240, in the cited local/global example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  NormSmoothFields NormAnalyticUP NormAnalyticFlatLocal ScalarRightLittleOPower ScalarRightFlatJets
  FlatExponentialSealed FlatExponentialRightDecay.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_right_flat_analytic_locally_zero]:
    the actual finite-order-versus-flatness bridge supporting
    the example cited at 3.4.5, p. 321. Every
    derivative at the endpoint is proved zero before the
    existing analytic Taylor theorem supplies a zero neighbourhood. *)
Theorem scalar_right_flat_analytic_locally_zero (R:realType) (A:set R) (f:R->R):
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) A f 0 ->
  (forall m,scalar_right_little_o_power f m) ->
  exists U:set R,U 0 /\U `<=` A /\
    @open (real_norm_metric_space (@scalar_absolute_value_norm R)) U /\
    forall t,U t ->f t=0.
Proof.
move=>[V [c [hV0 [hVA [hSmooth hBound]]]]] hFlat.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose NZ i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have [D hD]:=@norm_smooth_fields_exist R R^o R^o N N hN hN V f hSmooth.
have hZero:=@scalar_smooth_right_flat_jets R V f D hV0
  (norm_class_continuous (hSmooth 0%N)) (fun i=>(hD i).1) (fun i=>(hD i).2) hFlat.
have hAnalyticV:@norm_analytic_at R R^o R^o N N hN hN V f 0.
  exists V,c;split;first exact:hV0.
  split;first by move=>x hx.
  by split.
have hAllZero i (z:Z i):has_norm_higher_differential N ev NZ V f i 0 z ->z=0.
  move=>hz.
  have hEqual:=@norm_higher_differential_unique R R^o R^o N N hN hN
    Z ev NZ hZ V f i 0 z (D i 0) hz ((hD i).1 0 hV0).
  by rewrite hEqual hZero.
have [U [hU0 [hUV [hInterior hValue]]]]:=@norm_analytic_flat_locally_zero
  R R^o R^o N N hN hN V f 0 hAnalyticV hAllZero.
exists U;split;first exact:hU0.
split;first by move=>x hx;exact:hVA x (hUV x hx).
split;last exact:hValue.
rewrite openE=>x hx.
exact:((@norm_domain_interior_neighbourhood R R^o N hN U x).1 (hInterior x hx)).
Qed.

(** Source for [analytic_bounded_flat_exponential_locally_zero]:
    an actual analytic coefficient bounded by a finite multiple
    of the proved flat exponential is zero near the endpoint,
    supporting the example cited in 3.4.5, p. 321. *)
Theorem analytic_bounded_flat_exponential_locally_zero (R:realType)
    (A:set R) (f:R->R) (C r:R):
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) A f 0 ->
  0<=C ->0<r ->
  (forall t:R,0<t<r ->`|f t|<=C*FlatExponential.value t) ->
  exists U:set R,U 0 /\U `<=` A /\
    @open (real_norm_metric_space (@scalar_absolute_value_norm R)) U /\
    forall t,U t ->f t=0.
Proof.
move=>hAnalytic hC hr hBound.
exact:(@scalar_right_flat_analytic_locally_zero R A f hAnalytic
  (@bounded_flat_exponential_right_decay R f C r hC hr hBound)).
Qed.
