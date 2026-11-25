(** Federer (1969), 4.1.4, p. 349: the actual smoothed
    dual density is constant on each connected C_e when its
    coordinate derivatives vanish. This zero-differential
    inference reuses 3.1.18's proved local rank-zero theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  LinearRankUP NormRankZero ConnectedLocalConstancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_connected_zero_differential_constant]:
    an actual zero differential gives constancy on the original
    connected open set, the inference in Federer 4.1.4, p. 349.
    Neither target completeness nor finite dimension is needed. *)
Theorem norm_connected_zero_differential_constant (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (f:X->Y):
  @connected (real_norm_metric_space hNX) A ->
  (forall x,A x ->has_norm_differential NX NY A f x (0:Hom X Y)) ->
  forall a b,A a ->A b ->f b=f a.
Proof.
move=>hConnected hD.
have hRank:has_linear_rank (0:Hom X Y) 0%N.
  apply:(linear_rank_zeroP (0:Hom X Y)).2=>v; exact:hom_zeroE.
have hLocal x:A x ->nbhs (x:real_norm_metric_space hNX) [set z|A z /\ f z=f x].
  move=>hx.
  have hGeneric:norm_generic_rank NX A (fun _:X=>(0:Hom X Y)) x 0%N.
    have[d [hd hBall]]:=norm_differential_interior (hD x hx).
    exists d; split=>// h hh; split; first exact:hBall h hh.
    exact hRank.
  have[r [hr hConstant]]:=@norm_generic_rank_zero_locally_constant R X Y NX NY hNX hNY
    A f (fun _:X=>(0:Hom X Y)) x hD hGeneric.
  apply/(metricType_numDomainType.nbhs_mdistP (x:real_norm_metric_space hNX) _).
  exists r; first exact hr.
  move=>z hz; apply:hConstant.
  change (is_true (NX (x-z)<r)) in hz.
  by rewrite (real_seminorm_subtract hNX.1).
exact:(@connected_local_constancy [the topologicalType of real_norm_metric_space hNX]
  (Y:Type) A f hConnected hLocal).
Qed.
