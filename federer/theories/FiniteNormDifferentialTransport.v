(** Federer (1969), 3.2.28(1), printed p. 263: the actual
    Gram differential is the same linear map for the operator
    and Hom inner-product norms. This finite-norm transport
    preserves the original function, differential and domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom TensorUP RealNormUP LinearBasis
  NormDifferentialUP NormFiniteLinearBound NormLinearDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_finite_norm_change]: norm
    independence of the finite-dimensional differential used
    in Federer 3.2.28(1), p. 263, from the norm-equivalence
    assertion recalled in 2.7.16, p. 134. The proof
    transfers the full epsilon remainder, not just existence. *)
Theorem norm_differential_finite_norm_change (R:realType) (X Y:lmodType R)
    (NX MX:X->R) (NY MY:Y->R)
    (hNX:is_real_norm NX) (hMX:is_real_norm MX)
    (hNY:is_real_norm NY) (hMY:is_real_norm MY)
    n (b:'I_n->X) (hb:is_basis b) p (c:'I_p->Y) (hc:is_basis c)
    (A:X->Prop) (f:X->Y) a (L:Hom X Y):
  has_norm_differential NX NY A f a L ->
  has_norm_differential MX MY A f a L.
Proof.
move=>hf.
have hIn:=norm_finite_linear_bounded hMX hNX hb (hom_of_linear (linear_id X)).
have hOut:=norm_finite_linear_bounded hNY hMY hc (hom_of_linear (linear_id Y)).
have [C [hC hCi]]:=hIn; have [D [hD hDo]]:=hOut.
have hInput x:NX x<=C*MX x:=hCi x.
have hOutput y:MY y<=D*NY y:=hDo y.
constructor.
- exact:(@norm_bounded_linear_preimage_interior R X X MX NX hMX
    (hom_of_linear (linear_id X)) A a hIn (norm_differential_interior hf)).
- have [M [hM hL]]:=norm_differential_bounded hf.
  exists (D*M*C); split; first by rewrite !mulr_ge0.
  move=>h; apply:le_trans (hOutput (L h)) _.
  apply:le_trans (ler_wpM2l hD (hL h)) _.
  have hb':=ler_wpM2l (mulr_ge0 hD hM) (hInput h).
  by rewrite !mulrA in hb' *.
- move=>e he.
  have hCp:0<C+1 by lra.
  have hDp:0<D+1 by lra.
  have hDen:0<(D+1)*(C+1):=mulr_gt0 hDp hCp.
  pose q:=e/((D+1)*(C+1)).
  have hq:0<q by rewrite /q divr_gt0.
  have [d [hd hrem]]:=norm_differential_remainder hf hq.
  exists (d/(C+1)); split; first by rewrite divr_gt0.
  move=>h ha hh.
  have hn:=real_seminorm_nonnegative hMX.1 h.
  have hSmall:(C+1)*MX h<d by move:hh; rewrite ltr_pdivlMr // mulrC.
  have hCStep:C<=C+1 by lra.
  have hStep:=ler_wpM2r hn hCStep.
  have hOld:NX h<d:=le_lt_trans (le_trans (hInput h) hStep) hSmall.
  apply:le_trans (hOutput _) _.
  apply:le_trans (ler_wpM2l hD (hrem h ha hOld)) _.
  rewrite mulrA.
  apply:le_trans (ler_wpM2l (mulr_ge0 hD (ltW hq)) (hInput h)) _.
  have hValue:q*((D+1)*(C+1))=e by rewrite /q divfK // (gt_eqF hDen).
  have hD1:D<=D+1 by lra.
  have hC1:C<=C+1 by lra.
  have hDC:D*C<=(D+1)*(C+1):=ler_pM hD hC hD1 hC1.
  have hProd:=ler_wpM2l (ltW hq) hDC.
  rewrite hValue in hProd.
  have hCoef:D*q*C<=e.
    have hAlg:D*q*C=q*(D*C) by ring.
    by rewrite hAlg.
  have hb':=ler_wpM2r hn hCoef.
  by rewrite !mulrA in hb' *.
Qed.
