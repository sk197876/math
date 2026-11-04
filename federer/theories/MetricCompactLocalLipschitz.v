(** Federer (1969), 3.2.47, p. 283: supporting finite
    Lipschitz control of a smooth product coordinate on a
    compact part of its original domain. This metric compactness
    lemma bounds nearby pairs in one local patch and separated
    pairs by the original bounded image. It imposes no
    connectedness, convexity or finite-dimensional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  finmap classical_sets topology lra.
From Federer Require Import CoveringFamilyUP MetricClosedBalls CompactFiniteCover
  LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_compact_local_lipschitz]: supporting
    compact-domain Lipschitz bound for the actual H_e in
    3.2.47, pp. 282–283. Local finite bounds and
    an actual image-diameter bound imply one finite bound on K. *)
Theorem metric_compact_local_lipschitz (R:realType) (X Y:metricType R)
    (K:set X) (f:X->Y) (M:R):
  compact K ->0<=M ->(forall x y,K x ->K y ->mdist (f x) (f y)<=M) ->
  (forall c,K c ->exists r L,0<r /\
    is_metric_lipschitz_bound (@metric_open_ball R X c r) f L) ->
  is_metric_lipschitz K f.
Proof.
move=>hK hM hImage hLocal.
have hex c:exists p:R*R,0<p.1 /\0<=p.2 /\
    (K c ->is_metric_lipschitz_bound (@metric_open_ball R X c p.1) f p.2).
  case:(pselect (K c))=>hc.
  - have [r [L [hr hBound]]]:=hLocal c hc.
    exists (r,L); split; first exact hr.
    split; first exact hBound.1.
    by move=>_.
  - exists (1,0); split; first exact:ltr01.
    split; first exact:lexx.
    by move=>/hc.
have [p hP]:=choice hex.
have hCover:K `<=` \bigcup_(c in K) [set y|mdist c y<(p c).1/2].
  move=>x hx; exists x; first exact hx.
  by rewrite /= mdistxx divr_gt0 //; exact:(hP x).1.
have [F hFK hF]:=@compact_open_finite_cover X X K
  (fun c=>[set y|mdist c y<(p c).1/2]) K hK
  (fun c _=>@metric_open_ball_open R X c ((p c).1/2)) hCover.
pose d:=\big[Order.min/1]_(i:F) ((p (val i)).1/2).
have hd:0<d.
  rewrite /d; apply:(big_ind (fun z:R=>0<z)).
  - exact:ltr01.
  - by move=>u v hu hv; rewrite lt_min hu hv.
  - move=>i _; by rewrite divr_gt0 //; exact:(hP (val i)).1.
have hdc c: c \in F ->d<=(p c).1/2.
  move=>hcf; exact:(bigmin_le 1 [` hcf]%fset (fun i:F=>(p (val i)).1/2)).
pose S:=\sum_(i:F) (p (val i)).2.
have hS:0<=S by apply:sumr_ge0=>i _; exact:(hP (val i)).2.1.
have hterm (i:F):(p (val i)).2<=S.
  rewrite /S (bigD1 i) //= lerDl.
  apply:sumr_ge0=>j _; exact:(hP (val j)).2.1.
have hQuot:0<=M/d:=divr_ge0 hM (ltW hd).
have hConstant:0<=S+M/d:=addr_ge0 hS hQuot.
apply:(@metric_lipschitz_of_bound R X Y K f (S+M/d)); split; first exact hConstant.
move=>x y hx hy.
case:(ltP (mdist x y) d)=>[hSmall|hFar].
- have [c hcf hcx]:=hF x hx.
  have hkc:K c:=set_mem (hFK c hcf).
  change (is_true (mdist c x<(p c).1/2)) in hcx.
  have hcy:mdist c y<(p c).1.
    have hTriangle:=metric_triangle c x y.
    have hxy:=lt_le_trans hSmall (hdc c hcf).
    lra.
  have hcxr:mdist c x<(p c).1.
    have hPositive:0<(p c).1:=(hP c).1; lra.
  have hBound:=((hP c).2.2 hkc).2 x y hcxr hcy.
  have hLe: (p c).2<=S+M/d.
    have hTerm:=hterm ([` hcf]%fset).
    change (is_true ((p c).2<=S)) in hTerm; lra.
  exact:(le_trans hBound (ler_wpM2r (mdist_ge0 x y) hLe)).
- have hLower:M<=(M/d)*mdist x y.
    have hProduct:=ler_wpM2l hQuot hFar.
    by rewrite divfK ?gt_eqF in hProduct.
  have hLe:M/d<=S+M/d by rewrite lerDr.
  exact:(le_trans (hImage x y hx hy) (le_trans hLower
    (ler_wpM2r (mdist_ge0 x y) hLe))).
Qed.
