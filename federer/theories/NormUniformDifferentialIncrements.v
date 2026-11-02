(** Federer (1969), 3.1.24, pp. 238–239:
    uniform convergence of differentials controls the increments
    of the limiting series. This supports termwise differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormDifferentialSubtraction
  InnerConvex NormDifferentialConvexBound NormSequenceClosedBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_uniform_differential_increment_error]: supporting
    the induction for termwise differentiation in Federer 3.1.24,
    pp. 238–239. On a convex domain, a uniform error
    e in the derivative field bounds the increment error
    of a partial sum by 2e times the input distance.
    The value convergence need only be pointwise. *)
Lemma norm_uniform_differential_increment_error (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (F:nat->X->Y) (D:nat->X->Hom X Y) (f:X->Y)
    (L:X->Hom X Y) e n :
  is_inner_convex A -> 0<=e ->
  (forall N x,A x -> has_norm_differential NX NY A (F N) x (D N x)) ->
  (forall x,A x -> forall eps:R,0<eps -> exists k:nat,
    forall N,(k<=N)%N -> NY (F N x-f x)<eps) ->
  (forall N,(n<=N)%N -> forall x,A x -> forall v,
    NY ((D N x-L x) v)<=e*NX v) ->
  forall N,(n<=N)%N -> forall x y,A x -> A y ->
    NY ((f x-F N x)-(f y-F N y))<=2*e*NX (x-y).
Proof.
move=>hA he hd hc hb N hN x y hx hy.
have hbound M (hM:(n<=M)%N):
    NY ((F M x-F N x)-(F M y-F N y))<=2*e*NX (x-y).
  have htwo:0<=2*e by apply: mulr_ge0=>//; exact: ler0n.
  apply: (@norm_differential_convex_bound R X Y NX NY hNX hNY A A
    (fun z=>F M z-F N z) (2*e) hA htwo _ x y hx hy).
  move=>z hz; exists (D M z-D N z); split.
  - exact (@norm_differential_subtract R X Y NX NY hNX hNY A
      (F M) (F N) z (D M z) (D N z) (hd M z hz) (hd N z hz)).
  - move=>v.
    have hid:(D M z-D N z) v= (D M z-L z) v-(D N z-L z) v.
      by rewrite !(linB (@hom_eval_linear R X Y v)) opprB addrA subrK.
    rewrite hid.
    have ht:=real_seminorm_triangle hNY.1 ((D M z-L z) v) (-((D N z-L z) v)).
    rewrite (real_seminorm_negate hNY.1) in ht.
    apply: le_trans ht _.
    have hh:=lerD (hb M hM z hz v) (hb N hN z hz v).
    have heq:e*NX v+e*NX v= 2*e*NX v by ring.
    by rewrite heq in hh.
have hxc:forall eps:R,0<eps -> exists k:nat,forall M,(k<=M)%N ->
    NY ((F M x-F N x)-(f x-F N x))<eps.
  move=>eps heps; have [k hk]:=hc x hx eps heps.
  exists k=>M hM.
  have heq:(F M x-F N x)-(f x-F N x)= F M x-f x.
    by rewrite opprB addrA subrK.
  by rewrite heq; exact (hk M hM).
have hyc:forall eps:R,0<eps -> exists k:nat,forall M,(k<=M)%N ->
    NY ((F M y-F N y)-(f y-F N y))<eps.
  move=>eps heps; have [k hk]:=hc y hy eps heps.
  exists k=>M hM.
  have heq:(F M y-F N y)-(f y-F N y)= F M y-f y.
    by rewrite opprB addrA subrK.
  by rewrite heq; exact (hk M hM).
have hconv:=@norm_sequence_limit_difference R Y NY hNY.1
  (fun M=>F M x-F N x) (fun M=>F M y-F N y)
  (f x-F N x) (f y-F N y) hxc hyc.
exact (@norm_sequence_limit_closed_bound R Y NY hNY.1
  (fun M=>(F M x-F N x)-(F M y-F N y))
  ((f x-F N x)-(f y-F N y)) (2*e*NX (x-y)) n hconv hbound).
Qed.
