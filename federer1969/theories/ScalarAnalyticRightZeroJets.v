(** Federer (1969), 3.4.5, p. 321: an actual
    analytic scalar function zero immediately to the right
    has zero actual jets at the endpoint. This uses
    the Taylor identity in 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialUP NormHigherDifferentialLocal NormHigherDifferentialUnique NormHigherDifferentialSupport
  NormAnalyticUP ScalarRightLittleOPower ScalarRightFlatAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_analytic_right_zero_jets]: vanishing
    on an original positive interval forces every actual
    endpoint differential to vanish, supporting 3.4.5, p. 321.
    Neither a formal jet nor the desired zero jet is assumed. *)
Theorem scalar_analytic_right_zero_jets (R:realType) (A:set R^o) (f:R->R) (r:R):
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) A f 0 ->
  0<r ->(forall t,0<t<r ->f t=0) ->
  forall m (z:@ContinuousMultilinear.space R m R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)),
    has_norm_higher_differential (fun t:R^o=>`|t|)
      (fun i=>@ContinuousMultilinear.evaluation R i R^o R^o (fun t=>`|t|) (fun t=>`|t|)
        (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R))
      (fun i=>@ContinuousMultilinear.norm R i R^o R^o (fun t=>`|t|) (fun t=>`|t|)
        (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)) A f m 0 z ->z=0.
Proof.
move=>hAnalytic hr hZero.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o N N hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o N N hN hN.
pose NZ i:=@ContinuousMultilinear.norm R i R^o R^o N N hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o N N hN hN.
have hFlat m:scalar_right_little_o_power f m.
  move=>epsilon hEpsilon;exists r;split;first exact:hr.
  move=>t ht;rewrite hZero // normr0.
  apply:mulr_ge0;first exact:ltW hEpsilon.
  apply:exprn_ge0;exact:ltW (andP ht).1.
have [U [hU0 [hUA [hOpen hValues]]]]:=scalar_right_flat_analytic_locally_zero hAnalytic hFlat.
have hInterior t (ht:U t):norm_domain_interior N U t.
  apply:(@norm_domain_interior_neighbourhood R R^o N hN U t).2.
  exact:(open_nbhs_nbhs (conj hOpen ht)).
move=>m z hz.
have hGlobal:has_norm_higher_differential N ev NZ setT f m 0 z.
  apply:(@norm_higher_differential_local_agreement R R^o R^o N N hN hN Z ev NZ hZ m
    A setT U f f hInterior _ _ 0 hU0 z).1 hz.
  - by move=>t ht;split=>_;[exact:Logic.I|exact:hUA t ht].
  - by move=>t ht _.
have hZeroJet:=@norm_higher_differential_locally_zero R R^o R^o N N hN hN Z ev NZ hZ U f m 0
  hInterior hValues hU0.
exact:(norm_higher_differential_unique hN hN hZ hGlobal hZeroJet).
Qed.
