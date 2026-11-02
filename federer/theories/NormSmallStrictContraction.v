(** Federer (1969), 3.2.35, p. 271:
    strict radial contractions approximate each point,
    supporting the closure and gauge-boundary identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_small_strict_contraction]: supporting
    closure of the strict unit gauge sublevel
    in Federer 3.2.35, p. 271. Every
    positive norm neighbourhood of x contains t*x
    for some 0<t<1, including at x=0.
    This normed-space helper selects its parameter
    locally and needs no compactness or dimension. *)
Lemma norm_small_strict_contraction (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (x:V) d:
  0<d ->exists t:R,0<t /\t<1 /\N (t*:x-x)<d.
Proof.
move=>hd.
have hNx:0<=N x:=real_seminorm_nonnegative hN.1 x.
have hDenominator:0<N x+1 by lra.
pose q:R:=d/(N x+1).
have hq:0<q by rewrite /q divr_gt0.
pose m:R:=Num.min 1 q.
have hm:0<m by rewrite /m lt_min ltr01 hq.
have hm1:m<=1 by rewrite /m ge_min lexx.
have hmq:m<=q by rewrite /m ge_min lexx orbT.
pose e:R:=m/2.
have he:0<e by rewrite /e divr_gt0 // ltr0n.
have he1:e<1 by rewrite /e; lra.
have heq:e<q by rewrite /e; lra.
have hProduct:e*(N x+1)<d.
  by move:heq; rewrite /q ltr_pdivlMr.
have hSmall:e*N x<d by nra.
pose t:R:=1-e.
have ht0:0<t by rewrite /t subr_gt0.
have ht1:t<1 by rewrite /t; lra.
have hVector:t*:x-x= -e*:x.
  rewrite -{2}(scale1r x) -scalerBl /t.
  congr (_*:x); by rewrite addrAC subrr add0r.
exists t; split; first exact ht0; split; first exact ht1.
by rewrite hVector (real_seminorm_scale hN.1) normrN (ger0_norm (ltW he)).
Qed.
