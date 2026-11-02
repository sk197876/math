(** Federer (1969), 3.1.24, pp. 238–239:
    the higher-order step for termwise differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerConvex
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP NormHigherDifferentialFields
  NormBoundedBilinearUP MultilinearSuccessorArguments NormSuccessorContractionBound
  NormUniformDifferentialLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_fields_uniform_step]: supporting
    the induction with respect to i in Federer 3.1.24,
    p. 239. Uniform limits G_i and G_(i+1) of
    actual higher differential fields satisfy D G_i=G_(i+1),
    with the latter equality interpreted by the successor
    evaluation law. The first-order limit theorem proves the
    derivative claim; no convergence-of-derivatives hypothesis is
    substituted for actual differentiability. *)
Theorem norm_higher_fields_uniform_step (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A:X->Prop) (F:nat->X->Y) (D:forall N:nat,forall i,X->Z i)
    (G:forall i,X->Z i) k :
  is_inner_convex A ->
  (forall N i x,A x -> has_norm_higher_differential NX ev ZN A (F N) i x (D N i x)) ->
  (forall i,forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,A x -> @ZN i (D N i x-G i x)<eps) ->
  forall a,A a -> exists L:Hom X (Z k),
    has_norm_differential NX (@ZN k) A (G k) a L /\
    forall u v,@ev k u (L v)= @ev k.+1 (multilinear_successor_arguments u v) (G k.+1 a).
Proof.
move=>hA hd hu.
have hNk:=continuous_multilinear_norm_is_norm hNY (hZ k).
have [C [hC [hCb hCe]]]:=@continuous_multilinear_successor_contraction_unit_bound R k X Y NX NY hNX
  Z ev ZN hZ.
pose L N x:=@HomMap R X (Z k) (fun v=>C (D N k.+1 x) v)
  (introT (asboolP _) ((hC.1).2 (D N k.+1 x))).
pose M x:=@HomMap R X (Z k) (fun v=>C (G k.+1 x) v)
  (introT (asboolP _) ((hC.1).2 (G k.+1 x))).
have hdN N x (hx:A x):has_norm_differential NX (@ZN k) A (D N k) x (L N x).
  have [T [hT heT]]:=@norm_higher_differential_field_step_elim R X Y NX hNX
    Z ev ZN A (F N) k (D N k) x (D N k.+1 x) (hd N k) (hd N k.+1 x hx).
  have hTL:T= L N x.
    apply: hom_ext=>v; apply: (continuous_multilinear_extensional (hZ k))=>u.
    rewrite heT.
    symmetry; exact (hCe (D N k.+1 x) v u).
  by rewrite -hTL.
have hMb x (_:A x):norm_bounded_linear NX (@ZN k) (M x).
  exists (@ZN k.+1 (G k.+1 x)); split.
  - exact: multilinear_operator_nonnegative (continuous_multilinear_norm_laws (hZ k.+1) _).
  - move=>v; exact (hCb (G k.+1 x) v).
have hpoint x (hx:A x) eps (he:0<eps):exists n:nat,forall N,(n<=N)%N ->
    @ZN k (D N k x-G k x)<eps.
  have [n hn]:=hu k eps he.
  exists n=>N hN; exact (hn N hN x hx).
have hunif eps (he:0<eps):exists n:nat,forall N,(n<=N)%N -> forall x,A x ->
    forall v,@ZN k ((L N x-M x) v)<=eps*NX v.
  have [n hn]:=hu k.+1 eps he.
  exists n=>N hN x hx v.
  change (@ZN k (C (D N k.+1 x) v-C (G k.+1 x) v)<=eps*NX v).
  rewrite -(linB ((hC.1).1 v)).
  apply: le_trans (hCb (D N k.+1 x-G k.+1 x) v) _.
  exact (ler_wpM2r (real_seminorm_nonnegative hNX.1 v) (ltW (hn N hN x hx))).
have hlim:=@norm_uniform_differential_limit R X (Z k) NX (@ZN k) hNX hNk A
  (fun N=>D N k) L (G k) M hA hdN hMb hpoint hunif.
move=>a ha; exists (M a); split; first exact (hlim a ha).
move=>u v; exact (hCe (G k.+1 a) v u).
Qed.
