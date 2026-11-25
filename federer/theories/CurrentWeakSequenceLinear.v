(** Federer (1969), 4.1.14, pp. 370–371: linearity
    of the normal-current image follows by applying every
    original test to a common smooth approximation. The
    weak limit preserves every real linear combination;
    no compactness or measure representation is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentPointEvaluation CurrentWeakSequenceLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_weak_sequence_limit_linear]: the
    linearity passage used for the extension in Federer
    4.1.14, pp. 370–371. Original weak convergence is
    tested on every original compact smooth form. *)
Theorem current_weak_sequence_limit_linear (R:realType) (h2:(1+1:R)!=0)
    n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (u v:nat->@current_space R h2 n U hU m)
    (T S:@current_space R h2 n U hU m) (c:R):
  @is_current_weak_sequence_limit R h2 n m U hU u T ->
  @is_current_weak_sequence_limit R h2 n m U hU v S ->
  @is_current_weak_sequence_limit R h2 n m U hU
    (fun i=>c*:u i+v i) (c*:T+S).
Proof.
move=>hUSeq hVSeq phi epsilon hEpsilon.
pose E:=@current_point_evaluation R h2 n m U hU phi.
pose delta:=epsilon/(2*(`|c|+1)).
have hAbs:0<=`|c| :=normr_ge0 c.
have hTwo:0<(2:R) by rewrite ltr0n.
have hOne:0<`|c|+1 by lra.
have hDen:0<2*(`|c|+1):=mulr_gt0 hTwo hOne.
have hDelta:0<delta by rewrite /delta divr_gt0.
have[k hk]:=hUSeq phi delta hDelta.
have[l hl]:=hVSeq phi delta hDelta.
exists(maxn k l)=>i hNi.
have hA:=hk i (leq_trans (leq_maxl _ _) hNi).
have hB:=hl i (leq_trans (leq_maxr _ _) hNi).
have hDifference:E (c*:u i+v i)-E (c*:T+S)=
    c*(E (u i)-E T)+(E (v i)-E S).
  rewrite !(linearP E).
  change ((c*E (u i)+E (v i))-(c*E T+E S)=
    c*(E (u i)-E T)+(E (v i)-E S)).
  by ring.
change (is_true (`|E (c*:u i+v i)-E (c*:T+S)|<epsilon)).
rewrite hDifference.
apply:(le_lt_trans (ler_normD _ _)).
rewrite normrM.
have hFirst:=ler_wpM2l hAbs (ltW hA).
have hStrict:`|c|*delta+`|E (v i)-E S|<(`|c|+1)*delta.
  rewrite mulrDl mul1r ltrD2l; exact:hB.
have hEndpoint:(`|c|+1)*delta=epsilon/2.
  have hEnd:delta*(2*(`|c|+1))=epsilon by rewrite /delta divfK ?gt_eqF.
  nra.
rewrite hEndpoint in hStrict.
have hHalf:epsilon/2<epsilon by lra.
exact:le_lt_trans (lerD hFirst (lexx _)) (lt_trans hStrict hHalf).
Qed.
