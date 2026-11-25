(** Federer (1969), 3.2.33, p. 270: geometric
    domination of the powers multiplying each derivative of
    the rescaled interval bump. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import EventualGeometricDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [shrinking_interval_derivative_weights_geometric]:
    supporting normal convergence of every differentiated series
    in Federer 3.2.33, p. 270. A rescaled term indexed
    from zero has derivative bound C d_j^(j+1) d_j^(-i).
    Lengths at most q<1 give a uniform geometric bound
    after i terms; the finite prefix is absorbed explicitly.
    No positive lower bound on interval lengths is assumed. *)
Lemma shrinking_interval_derivative_weights_geometric (R:realType)
    (d:nat->R) q C i:
  0<q<1 ->0<=C ->(forall j,0<d j<=q) ->
  exists M:R,0<M /\forall j,C*(d j)^+j.+1*((d j)^-1)^+i<=q^+j*M.
Proof.
move=>/andP [hq0 hq1] hC hD.
have hC0:0<=C*(q^-1)^+i by apply:mulr_ge0=>//; apply:exprn_ge0; rewrite invr_ge0; exact:ltW hq0.
apply:(eventual_geometric_domination hq0 hC0 (N:=i)).
move=>j hij.
have /andP [hd0 hdq]:=hD j.
have hdN:d j!= 0 by rewrite gt_eqF.
have hqN:q!= 0 by rewrite gt_eqF.
have hj:j= (j-i+i)%N by rewrite subnK.
have hCancel:(d j)^+j.+1*((d j)^-1)^+i= (d j)^+(j-i).+1.
  have hExp:j.+1= ((j-i).+1+i)%N by rewrite addSn subnK.
  rewrite hExp exprD exprVn mulfK ?expf_neq0 //.
have hBound:(d j)^+(j-i).+1<=q^+(j-i).+1.
  exact:(lerXn2r (j-i).+1 (ltW hd0) (ltW hq0) hdq).
have hTail:(d j)^+(j-i).+1<=q^+(j-i).
  apply:le_trans hBound _; rewrite exprS.
  have hPow:0<=q^+(j-i):=exprn_ge0 _ (ltW hq0).
  by rewrite -{2}[q^+(j-i)]mul1r (ler_wpM2r hPow (ltW hq1)).
have hQCancel:q^+j*(q^-1)^+i= q^+(j-i).
  have hPow:q^+j= q^+(j-i)*q^+i by rewrite -exprD subnK.
  rewrite hPow exprVn mulfK ?expf_neq0 //.
rewrite -mulrA hCancel.
have hScaled:=ler_wpM2l hC hTail.
rewrite -hQCancel in hScaled.
have hCoeff:C*(q^+j*(q^-1)^+i)= q^+j*(C*(q^-1)^+i).
  by rewrite mulrCA.
rewrite hCoeff in hScaled; exact hScaled.
Qed.
