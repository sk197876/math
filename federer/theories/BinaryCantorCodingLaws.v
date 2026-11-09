(** Federer (1969), 3.4.4, p. 318: original
    child containment and the two estimates at a first address split. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge BinaryCantorCodingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_coding_child_interval]: the
    two original endpoint children used in 3.4.4, p. 318.
    This derives their exact intervals from the independent coding
    laws; no child formula is supplied as a theorem premise. *)
Lemma binary_original_coding_child_interval (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->forall w b,
  val (I (rcons w b))=
    (`[a w+(if b then 1-rho else 0)*rho^+(size w),
       a w+(if b then 1-rho else 0)*rho^+(size w)+rho^+(size w)*rho]
      :set (real_line_metric R)).
Proof.
move=>h w b.
by rewrite (binary_original_coding_intervals h) (binary_original_coding_extension h)
  size_rcons exprSr.
Qed.

(** Source for [binary_original_coding_child_subset]: the
    nested original intervals in 3.4.4, p. 318.
    Every left or right child lies in its parent;
    this follows from the exact endpoint equations. *)
Lemma binary_original_coding_child_subset (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->0<=rho ->rho<=1 ->
  forall w b,val (I (rcons w b)) `<=` val (I w).
Proof.
move=>h hRho hUpper w b x hx.
move:hx;rewrite (binary_original_coding_child_interval h) /= in_itv /=.
rewrite (binary_original_coding_intervals h) /= in_itv /=.
have hPower:0<=rho^+(size w):=exprn_ge0 _ hRho.
have hSmall:=ler_wpM2l hPower hUpper.
rewrite mulr1 in hSmall.
case:b=>/= /andP[hLow hHigh];apply/andP;split;nra.
Qed.

(** Source for [binary_original_coding_prefix_subset]: a
    longer original address stays in every prefix interval,
    supporting the least-split argument in 3.4.4, p. 318. *)
Lemma binary_original_coding_prefix_subset (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->0<=rho ->rho<=1 ->
  forall u v,prefix u v ->val (I v) `<=` val (I u).
Proof.
move=>h hRho hUpper u v /prefixP[s ->].
elim/last_ind:s=>[|s b ih];first by rewrite cats0.
rewrite -cats1 catA cats1.
move=>x hx;apply:ih.
exact:(@binary_original_coding_child_subset R rho J H I a h hRho hUpper (u++s) b x hx).
Qed.

(** Source for [binary_original_coding_point_distance]: the
    image points in one original level-j interval have distance
    at most rho^j, the second estimate in 3.4.4, p. 318. *)
Lemma binary_original_coding_point_distance (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->forall w (x y:real_line_metric R),
  val (I w) x ->val (I w) y ->`|x-y|<=rho^+(size w).
Proof.
move=>h w x y hx hy.
move:hx hy;rewrite (binary_original_coding_intervals h) /= !in_itv /=.
move=>/andP[hXLow hXHigh] /andP[hYLow hYHigh].
rewrite ler_norml;apply/andP;split;lra.
Qed.

(** Source for [binary_original_coding_sibling_gap]: the
    first estimate in 3.4.4, p. 318. Points in
    different original children of a common level-j interval
    are separated by (1-2 rho)rho^j. This retains
    the printed sharp gap, rather than a smaller generic
    equal-cost-tree bound. *)
Lemma binary_original_coding_sibling_gap (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->forall w (x y:real_line_metric R),
  val (I (rcons w false)) x ->val (I (rcons w true)) y ->
  (1-2*rho)*rho^+(size w)<=y-x /\
  (1-2*rho)*rho^+(size w)<=`|x-y|.
Proof.
move=>h w x y hx hy.
move:hx hy;rewrite !(binary_original_coding_child_interval h) /= !in_itv /=.
move=>/andP[hXLow hXHigh] /andP[hYLow hYHigh].
have hGap:(1-2*rho)*rho^+(size w)<=y-x by nra.
split;first exact:hGap.
have hAbs:y-x<=`|x-y|.
  have hNorm:=ler_norm (y-x).
  have hOpp:x-y= -(y-x) by rewrite opprB.
  rewrite hOpp normrN;exact:hNorm.
exact:le_trans hGap hAbs.
Qed.
