(** Federer (1969), 3.1.13, p. 224:
    every derivative of a compactly supported
    smooth function has a finite global norm
    bound. This supplies the bump constants G_i. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialSupport
  NormClassHigherUP NormClassHigherFields NormCompactFunctionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_compact_support_higher_differential_bound]:
    existence of finite derivative bounds G_i
    for the smooth radial cutoff in Federer
    3.1.13, p. 224. Compactness
    bounds each continuous derivative on K;
    locality makes it zero on the open complement. *)
Theorem norm_compact_support_higher_differential_bound (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (K : set X) (f : X->Y) k :
  compact [set x : real_norm_metric_space hNX | K x] ->
  (forall x, ~K x -> f x=0) ->
  norm_class_higher NX NY ev ZN (fun _=>True) f k ->
  exists (D : X->Z k) (M : R),
    (forall x, has_norm_higher_differential NX ev ZN (fun _=>True) f k x (D x)) /\
    0<M /\ (forall x, @ZN k (D x)<=M) /\
    forall x, ~K x -> D x=0.
Proof.
move=>hK hf hc.
have hNk := continuous_multilinear_norm_is_norm hNY (@hZ k).
have [_ [D [hD hcont]]] := hc.
have [M [hM hb]] := @norm_class_zero_compact_bounded R X (Z k) NX (@ZN k)
  hNX hNk (fun _=>True) K D hK (fun x _=>I) hcont.
have hclosed : @closed [the topologicalType of real_norm_metric_space hNX] K.
  exact: (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) hK).
have hopen := closed_openC hclosed.
have hO x (hx : ~K x) : norm_domain_interior NX (fun y=>~K y) x.
  apply: (norm_domain_interior_neighbourhood hNX (fun y=>~K y) x).2.
  by move:hopen; rewrite openE; apply.
have hzero x (hx : ~K x) : D x=0.
  have hz := @norm_higher_differential_locally_zero R X Y NX NY hNX hNY
    Z ev ZN hZ (fun y=>~K y) f k x hO hf hx.
  exact: (norm_higher_differential_unique hNX hNY hZ (hD x I) hz).
exists D, M; split; first by move=>x; exact: (hD x I).
split; first exact hM.
split; last exact hzero.
move=>x; case:(pselect (K x))=>[hx|hx]; first exact: (hb x hx).
by rewrite (hzero x hx) (real_seminorm_zero hNk.1); exact: (ltW hM).
Qed.
