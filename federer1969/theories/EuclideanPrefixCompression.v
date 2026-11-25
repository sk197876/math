(** Actual coordinate compression for the anisotropic tube
    argument in Federer (1969), 3.2.45, pp. 279–280.
    The norm calculation uses only 1.7.1, p. 28. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_diagonal_norm_bound]: supporting
    control of the actual compressed balls in Federer
    3.2.45, pp. 279–280. The original Euclidean
    squared norm, 1.7.1, p. 28, is the sum
    of the coordinate squares. Bounding every absolute
    diagonal coefficient by a bounds the norm by
    a times the original norm. Empty ambient spaces
    and a=0 are retained. *)
Lemma euclidean_diagonal_norm_bound (R : realType) n (c : 'I_n -> R) (a : R) (x : R_n R n) :
  0<=a -> (forall i, `|c i|<=a) ->
  inner_norm (@euclidean_inner_productP R n) (@euclidean_diagonal_map R n c x)<=
    a*inner_norm (@euclidean_inner_productP R n) x.
Proof.
move=> ha hC.
rewrite -(ler_sqr (inner_norm_nonnegative (@euclidean_inner_productP R n) _)
  (mulr_ge0 ha (inner_norm_nonnegative (@euclidean_inner_productP R n) _))).
rewrite inner_norm_sqr exprMn inner_norm_sqr /euclidean_inner_product mulr_sumr.
apply: ler_sum=> i _.
rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE.
have hSquare : (c i)^+2<=a^+2.
  have h : `|c i|^+2<=a^+2 by rewrite (ler_sqr (normr_ge0 (c i)) ha); exact: hC i.
  by rewrite -normrX (ger0_norm (sqr_ge0 _)) in h.
have hPositive : 0<=x i*x i by nra.
have h := ler_wpM2r hPositive hSquare.
move: h; rewrite !expr2; nra.
Qed.

(** Source for [euclidean_prefix_compression_difference]: supporting
    distance of each compressed point from its original
    vertical foot in Federer 3.2.45, pp. 279–280.
    Their actual difference has coefficients h in
    the first m coordinates and zero elsewhere.
    The bound holds for every real h and
    retains an empty block. *)
Lemma euclidean_prefix_compression_difference (R : realType) n m (h : R) (x : R_n R n) :
  inner_norm (@euclidean_inner_productP R n)
    (@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1) x-
     @euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1) x)<=
    `|h|*inner_norm (@euclidean_inner_productP R n) x.
Proof.
have hDifference :
    @euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1) x-
      @euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1) x=
    @euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 0) x.
  apply/ffunP=> j; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE.
  by case: (j<m)%N; rewrite ?mul0r ?subr0 ?subrr.
rewrite hDifference; apply: euclidean_diagonal_norm_bound; first exact: normr_ge0.
move=> j; case: (j<m)%N; first exact: lexx.
by rewrite normr0 normr_ge0.
Qed.

(** Source for [euclidean_prefix_zero_fixed]: supporting
    inclusion of the limiting vertical ball in every
    compressed ball for Federer 3.2.45, pp. 279–280.
    The original zero-first-block foot is fixed by
    every subsequent first-block diagonal scaling. *)
Lemma euclidean_prefix_zero_fixed (R : realType) n m (h : R) (x : R_n R n) :
  @euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)
    (@euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1) x)=
  @euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1) x.
Proof.
apply/ffunP=> j; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE.
by case: (j<m)%N; rewrite ?mul0r ?mulr0 ?mul1r.
Qed.

(** Source for [euclidean_prefix_zero_norm_bound]: supporting
    contraction of the limiting vertical foot in Federer
    3.2.45, pp. 279–280. Its actual diagonal
    coefficients are zero or one, so the proved
    Euclidean norm bound gives contraction, including
    either empty coordinate block. *)
Lemma euclidean_prefix_zero_norm_bound (R : realType) n m (x : R_n R n) :
  inner_norm (@euclidean_inner_productP R n)
    (@euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1) x)<=
    inner_norm (@euclidean_inner_productP R n) x.
Proof.
have h := @euclidean_diagonal_norm_bound R n (fun j => if (j<m)%N then 0 else 1) 1 x ler01.
rewrite mul1r in h; apply: h=> j.
by case: (j<m)%N; rewrite ?normr0 ?normr1 ?ler01.
Qed.
