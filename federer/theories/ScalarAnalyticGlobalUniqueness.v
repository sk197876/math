(** Federer (1969), 3.4.5, p. 321: global scalar
    analytic uniqueness used in the real proof of the cited
    example; the identity theorem is 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology HilbertFormCompactness
  NormAnalyticUP NormAnalyticFlatIdentity NormSpaceConnected ScalarRightLittleOPower
  ScalarRightFlatAnalytic ScalarAnalyticRightZeroJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_global_analytic_right_zero]: an
    actual global analytic function zero on an original
    positive interval is zero everywhere, supporting 3.4.5,
    p. 321, by the proved connected identity theorem. *)
Theorem scalar_global_analytic_right_zero (R:realType) (f:R->R) (r:R):
  @norm_analytic R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) setT f ->
  0<r ->(forall t,0<t<r ->f t=0) ->forall t,f t=0.
Proof.
move=>hf hr hZero t.
apply:(@norm_analytic_flat_identity R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
  (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) setT f 0
  (@real_norm_space_connected R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)) hf Logic.I
  (@scalar_analytic_right_zero_jets R setT f r (hf 0 Logic.I) hr hZero) t Logic.I).
Qed.

(** Source for [scalar_global_analytic_right_flat_zero]: an
    actual global analytic function flat to every order on
    the positive side is zero everywhere, supporting the
    actual Taylor argument of 3.4.5, p. 321. *)
Theorem scalar_global_analytic_right_flat_zero (R:realType) (f:R->R):
  @norm_analytic R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) setT f ->
  (forall m,scalar_right_little_o_power f m) ->forall t,f t=0.
Proof.
move=>hf hFlat.
have [U [hU0 [_ [hOpen hValue]]]]:=scalar_right_flat_analytic_locally_zero (hf 0 Logic.I) hFlat.
have [r [hr hBall]]:=(@norm_domain_interior_neighbourhood R R^o (fun t=>`|t|)
  (@scalar_absolute_value_norm R) U 0).2 (open_nbhs_nbhs (conj hOpen hU0)).
apply:(scalar_global_analytic_right_zero hf hr)=>t /andP[ht0 htr].
have ht:`|t|<r by rewrite ger0_norm ?(ltW ht0).
have hUt:=hBall t ht;rewrite add0r in hUt;exact:hValue t hUt.
Qed.
