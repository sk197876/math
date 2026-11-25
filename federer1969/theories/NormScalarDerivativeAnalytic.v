(** Federer (1969), 3.1.24, p. 240: scalar
    derivative sequences with factorial bounds verify the analytic
    scalar majorants used in the inverse argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP NormHigherDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearScalar ContinuousMultilinearSealed
  NormHigherDifferentialUnique ScalarDerivativeSequence NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_scalar_derivative_analytic_at]: supporting
    the scalar analytic inverse in Federer 3.1.24, p. 240.
    Ordinary successive derivatives on an actual neighbourhood,
    uniformly bounded by c^m m! in positive order, establish
    condition (1). The derivative-sequence criterion supplies the
    actual higher differentials and their continuity. *)
Theorem norm_scalar_derivative_analytic_at (R:realType)
    (U:R->Prop) (F:nat->R->R) a c :
  U a ->
  (forall m x,U x -> has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    U (F m) x (@scalar_coefficient_linear_map R R^o (F m.+1 x))) ->
  (forall m,(1<=m)%N -> forall x,U x -> `|F m x|<=c^+m*(m`!)%:R) ->
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) U (F 0%N) a.
Proof.
move=>ha hF hb.
pose hN:=scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN.
pose ev i:=@ContinuousMultilinear.evaluation R i R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN.
pose ZN i:=@ContinuousMultilinear.norm R i R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN.
pose hZ i:=@ContinuousMultilinear.laws R i R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN.
have hh m x (hx:U x):exists L:Hom R^o R^o,
    has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) U (F m) x L /\
    forall t,L t= t*F m.+1 x.
  exists (@scalar_coefficient_linear_map R R^o (F m.+1 x)); split; first exact (hF m x hx).
  by [].
have [D [hD [hE hc]]]:=@scalar_derivative_sequence_differentials R R^o
  (fun t:R^o=>`|t|) hN Z ev ZN hZ U F hh.
have hclass:=@scalar_derivative_sequence_class_infinity R R^o
  (fun t:R^o=>`|t|) hN Z ev ZN hZ U F hh.
exists U,c; split; first exact ha.
split; first by move=>x hx.
split; first exact hclass.
move=>m hm x hx z hz.
have heq:z= D m x:=@norm_higher_differential_unique R R^o R^o
  (fun t=>`|t|) (fun t=>`|t|) hN hN Z ev ZN hZ U (F 0%N) m x z (D m x) hz (hD m x hx).
rewrite heq (continuous_multilinear_scalar_norm hN (hZ m)) hE.
have hprod:(\prod_(i<m) ([ffun j:'I_m=>(1:R^o)]) i)= 1.
  by apply: big1=>i _; rewrite ffunE.
rewrite hprod; change (`|1*F m x|<=c^+m*(m`!)%:R).
by rewrite mul1r; exact: hb m hm x hx.
Qed.
