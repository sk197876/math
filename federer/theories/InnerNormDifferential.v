(** Federer (1969), 3.2.13, p. 250: the
    differential of the Euclidean norm away from zero.
    Prove its inner-product remainder estimate directly from
    the norm laws, before using polar integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import Hom Bilinear InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  HilbertFormCompactness NormDifferentialUP RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_reverse_triangle]: the
    unit Lipschitz bound for x mapped to |x| in
    Federer 3.2.13, p. 250, from 1.7.1.
    Supporting norm-law calculation in an arbitrary real inner-product space. *)
Lemma inner_norm_reverse_triangle (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (x y:V):
  `|inner_norm hB x-inner_norm hB y|<=inner_norm hB (x-y).
Proof.
have h1:=inner_norm_triangle hB (x-y) y.
have h2:=inner_norm_triangle hB (y-x) x.
rewrite subrK in h1.
rewrite subrK in h2.
have hOpp:inner_norm hB (y-x)=inner_norm hB (x-y).
  by rewrite -[y-x]opprB inner_normN.
rewrite hOpp in h2.
rewrite ler_norml; apply/andP; split.
- rewrite -lerN2 opprB opprK lerBlDr; exact h2.
- rewrite lerBlDr; exact h1.
Qed.

(** Source for [inner_norm_gradient_linear]: linearity of
    v mapped to (x dot v)/|x| in Federer
    3.2.13, p. 250. The formula is prescribed;
    its differentiability is proved only when x is nonzero. *)
Lemma inner_norm_gradient_linear (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (x:V):
  linear (fun v:V=>(inner_norm hB x)^-1*B x v:R^o).
Proof.
move=>c v w.
rewrite (bilDr (inner_bilinear hB)) (bilZr (inner_bilinear hB)) mulrDr.
by rewrite [(_^-1)*(c*_)]mulrCA.
Qed.

(** Source for [inner_norm_gradient]: the differential
    formula in Federer 3.2.13, p. 250,
    expressed as the existing abstract space of linear maps. *)
Definition inner_norm_gradient (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (x:V):Hom V R^o:=
  @HomMap R V R^o (fun v=>(inner_norm hB x)^-1*B x v)
    (introT (asboolP _) (inner_norm_gradient_linear hB x)).

(** Source for [inner_norm_differential]: the actual
    norm differential in Federer 3.2.13, p. 250.
    The quadratic remainder follows from the inner-product
    square identity and the reverse triangle inequality.
    No differentiability of a square-root implementation is assumed. *)
Theorem inner_norm_differential (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (a:V):
  a!= 0 ->has_norm_differential (inner_norm hB) (fun r:R^o=>`|r|) setT
    (fun x:V=>(inner_norm hB x:R^o)) a (inner_norm_gradient hB a).
Proof.
move=>ha.
pose N:=inner_norm hB.
pose b:=N a.
have hb:0<b by rewrite /b /N inner_norm_gt0.
have hbNe:b!= 0:=lt0r_neq0 hb.
have hInvPos:0<b^-1 by rewrite invr_gt0.
have hTwo:0<2*b by nra.
constructor.
- exists 1; split; first exact:ltr01; by move=>h hh.
- exists 1; split; first exact:ler01; move=>h.
  change (`|b^-1*B a h|<= 1*N h).
  rewrite normrM gtr0_norm ?invr_gt0 // mul1r.
  have hc:=inner_cauchy hB a h.
  have hh:=ler_wpM2l (ltW hInvPos) hc.
  by rewrite mulrA mulVf // mul1r in hh.
- move=>e he; exists (2*b*e); split; first exact:mulr_gt0 hTwo he.
  move=>h _ hSmall.
  pose z:=N (a+h)-b.
  pose err:=z-b^-1*B a h.
  have hReverse:`|z|<=N h.
    have hRev:=inner_norm_reverse_triangle hB (a+h) a.
    have hDiff:(a+h)-a=h by rewrite [a+h]addrC addrK.
    by rewrite hDiff in hRev.
  have hSquare:z^+2<=N h^+2.
    have hPow:=lerXn2r 2 (normr_ge0 z) (inner_norm_nonnegative hB h) hReverse.
    by rewrite -normrX ger0_norm ?sqr_ge0 in hPow.
  have hDiag:(N (a+h))^+2=b^+2+2*B a h+(N h)^+2.
    rewrite /b /N !inner_norm_sqr.
    rewrite (bilDl (inner_bilinear hB)) !(bilDr (inner_bilinear hB)) (inner_symmetric hB h a).
    ring.
  have hEq:(2*b)*err=(N h)^+2-z^+2.
    have hCancel:(2*b)*b^-1= 2 by rewrite -mulrA mulfV // mulr1.
    rewrite /err mulrBr mulrA hCancel /z.
    nra.
  have hNonnegative:0<=err.
    rewrite -(ler_pM2l hTwo) mulr0 hEq subr_ge0; exact hSquare.
  have hUpper:(2*b)*err<=(N h)^+2.
    rewrite hEq lerBlDr; have hSq:=sqr_ge0 z; lra.
  change (`|err|<=e*N h).
  rewrite ger0_norm // -(ler_pM2l hTwo).
  apply:le_trans hUpper _.
  have hProduct:=ler_wpM2r (inner_norm_nonnegative hB h) (ltW hSmall).
  rewrite expr2 mulrA; exact hProduct.
Qed.
