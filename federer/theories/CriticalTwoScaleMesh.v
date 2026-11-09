(** Federer (1969), 3.4.2(8), p. 316: choose actual
    positive subdivision counts with the required two mesh scales. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerContinuity UniformMeshCountUP
  UniformMeshCount UniformMeshCountLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_two_scale_mesh_exists]: the choice of
    alpha and beta in 3.4.2(8), p. 316. In addition to the
    printed bracket eps*(r/alpha)^lambda<=r/beta<=
    2*eps*(r/alpha)^lambda, the widths satisfy any prescribed
    positive source cutoff and image-diameter cutoff. The opaque
    integer mesh count supplies the witnesses; no rounding operation
    or asymptotic count is assumed. *)
Theorem critical_two_scale_mesh_exists (R:realType) a
    (r eps lambda delta N cap:R):
  0<r ->0<eps ->0<lambda ->0<delta ->0<N ->0<cap ->
  exists alpha beta:nat,exists h j:R,
    (0<alpha)%N /\(0<beta)%N /\0<h /\0<j /\
    alpha%:R*h=r /\beta%:R*j=r /\a%:R*h<=delta /\
    eps*real_power h lambda<=j /\j<= 2*eps*real_power h lambda /\N*j<=cap.
Proof.
move=>hr hEps hLambda hDelta hN hCap.
pose T:=Num.min r (cap/N).
have hT:0<T by rewrite /T lt_min hr divr_gt0.
have hTwoEps:0<2*eps by rewrite mulr_gt0 // ltr0n.
pose root:=real_power (T/(2*eps)) lambda^-1.
have hArgument:0<T/(2*eps) by rewrite divr_gt0.
have hRoot:0<root:=real_power_strictly_positive _ hArgument.
pose q:=Num.min (delta/(a%:R+1)) root.
have hAOne:0<(a%:R+1:R) by have hh:=ler0n R a;lra.
have hq:0<q by rewrite /q lt_min divr_gt0.
pose alpha:=uniform_mesh_count (ltW hr) hq.
have hAlpha:=uniform_mesh_count_specification (ltW hr) hq.
have hAlphaN:(0<alpha)%N:=uniform_mesh_count_positive_law hAlpha.
have hAlphaR:0<(alpha%:R:R) by rewrite ltr0n.
pose h:=r/alpha%:R.
have hh:0<h by rewrite /h divr_gt0.
have hSmall:h<=q:=uniform_mesh_count_cell_width hAlpha.
have hSource:h<=delta/(a%:R+1).
  apply:(le_trans hSmall);by rewrite /q ge_min lexx.
have hRootBound:h<=root.
  apply:(le_trans hSmall);by rewrite /q ge_min lexx orbT.
have hPower:real_power h lambda<=T/(2*eps).
  have hb:=real_power_monotone (ltW hh) hRootBound hLambda.
  have hCancel:real_power root lambda=T/(2*eps).
    exact:real_power_inverse_power (ltW hArgument) hLambda.
  by rewrite hCancel in hb.
pose mesh:= 2*eps*real_power h lambda.
have hMesh:0<mesh by rewrite /mesh mulr_gt0 //;exact:real_power_strictly_positive _ hh.
have hMeshT:mesh<=T.
  have hb:=ler_wpM2l (ltW hTwoEps) hPower.
  have hCancel:(2*eps)*(T/(2*eps))=T by field;by rewrite gt_eqF.
  by rewrite hCancel in hb.
have hMeshR:mesh<=r.
  apply:(le_trans hMeshT);by rewrite /T ge_min lexx.
have hMeshCap:mesh<=cap/N.
  apply:(le_trans hMeshT);by rewrite /T ge_min lexx orbT.
pose beta:=uniform_mesh_count (ltW hr) hMesh.
have hBeta:=uniform_mesh_count_specification (ltW hr) hMesh.
have hBetaN:(0<beta)%N:=uniform_mesh_count_positive_law hBeta.
have hBetaR:0<(beta%:R:R) by rewrite ltr0n.
pose j:=r/beta%:R.
have hj:0<j by rewrite /j divr_gt0.
have hJMesh:j<=mesh:=uniform_mesh_count_cell_width hBeta.
exists alpha,beta,h,j;split;first exact:hAlphaN.
split;first exact:hBetaN.
split;first exact:hh.
split;first exact:hj.
split;first by rewrite /h mulrC divfK ?gt_eqF.
split;first by rewrite /j mulrC divfK ?gt_eqF.
split.
- have hb:(a%:R+1)*h<=delta.
    have hb:=hSource;rewrite ler_pdivlMr // in hb.
    rewrite mulrC;exact:hb.
  have hExtra:0<=1*h by rewrite mul1r;exact:ltW hh.
  have hExpand:(a%:R+1)*h=a%:R*h+1*h by ring.
  rewrite hExpand in hb;lra.
split.
- rewrite /j ler_pdivlMr //.
  have hb:=uniform_mesh_count_upper_law hBeta.
  have hTwo:(beta%:R)*mesh<= 2*r by lra.
  have hExpand:beta%:R*mesh= 2*(eps*real_power h lambda*beta%:R) by rewrite /mesh;ring.
  rewrite hExpand in hTwo;lra.
split;first exact:hJMesh.
have hUpper:=le_trans hJMesh hMeshCap.
rewrite ler_pdivlMr // in hUpper.
rewrite mulrC;exact:hUpper.
Qed.
