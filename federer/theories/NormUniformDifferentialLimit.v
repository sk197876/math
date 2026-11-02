(** Federer (1969), 3.1.24, pp. 238–239:
    differentiating a limit when the differentials converge
    uniformly. This is the first-order step underlying the
    induction for the analytic polynomial series. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerConvex
  NormUniformDifferentialIncrements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_uniform_differential_limit]: supporting
    the termwise differentiation assertion of Federer 3.1.24,
    pp. 238–239. A pointwise limit of differentiable functions
    on an open convex domain has differential L when their
    differentials converge uniformly to the bounded field L.
    All hypotheses concern the actual common domain, and
    completeness is unnecessary once both limits are supplied. *)
Theorem norm_uniform_differential_limit (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (F:nat->X->Y) (D:nat->X->Hom X Y) (f:X->Y)
    (L:X->Hom X Y) :
  is_inner_convex A ->
  (forall N x,A x -> has_norm_differential NX NY A (F N) x (D N x)) ->
  (forall x,A x -> norm_bounded_linear NX NY (L x)) ->
  (forall x,A x -> forall eps:R,0<eps -> exists k:nat,
    forall N,(k<=N)%N -> NY (F N x-f x)<eps) ->
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,A x -> forall v,NY ((D N x-L x) v)<=eps*NX v) ->
  forall a,A a -> has_norm_differential NX NY A f a (L a).
Proof.
move=>hA hd hL hc hu a ha; constructor.
- exact: norm_differential_interior (hd 0%N a ha).
- exact: hL a ha.
- move=>eps heps.
  pose e:=eps/4.
  have he:0<e by rewrite /e divr_gt0 // ltr0n.
  have [n hn]:=hu e he.
  have [d [hd0 hr]]:=norm_differential_remainder (hd n a ha) he.
  exists d; split; first exact hd0.
  move=>h hah hh.
  have hinc:=@norm_uniform_differential_increment_error R X Y NX NY hNX hNY
    A F D f L e n hA (ltW he) hd hc hn n (leqnn n) (a+h) a hah ha.
  have hshift:(a+h)-a= h by rewrite addrAC subrr add0r.
  rewrite hshift in hinc.
  have hrem:=hr h hah hh.
  have hder:=hn n (leqnn n) a ha h.
  have hswap:(f (a+h)-F n (a+h))-(f a-F n a)=
      (f (a+h)-f a)-(F n (a+h)-F n a).
    rewrite !opprB (addrACA (f (a+h)) (-F n (a+h)) (F n a) (-f a))
      (addrACA (f (a+h)) (-f a) (F n a) (-F n (a+h))).
    by rewrite [(-F n (a+h))+(-f a)]addrC.
  have htwo:(F n (a+h)-F n a-D n a h)+(D n a-L a) h=
      F n (a+h)-F n a-L a h.
    by rewrite (linB (@hom_eval_linear R X Y h)) addrA subrK.
  have hid:f (a+h)-f a-L a h=
      ((f (a+h)-F n (a+h))-(f a-F n a))+
      ((F n (a+h)-F n a-D n a h)+(D n a-L a) h).
    by rewrite htwo hswap addrA subrK.
  rewrite hid.
  have ht:=real_seminorm_triangle hNY.1
    ((f (a+h)-F n (a+h))-(f a-F n a))
    ((F n (a+h)-F n a-D n a h)+(D n a-L a) h).
  apply: le_trans ht _.
  have ht2:=real_seminorm_triangle hNY.1 (F n (a+h)-F n a-D n a h) ((D n a-L a) h).
  have hlast:=le_trans ht2 (lerD hrem hder).
  have hs:=lerD hinc hlast.
  have heq:2*e*NX h+(e*NX h+e*NX h)= eps*NX h by rewrite /e; field.
  by rewrite heq in hs.
Qed.
