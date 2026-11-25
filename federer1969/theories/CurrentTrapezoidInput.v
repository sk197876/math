(** Federer (1969), 4.1.12, p. 369: prepare
    the original smooth cutoffs with derivative bound
    k^3. The already proved interval bump of
    2.5.17, p. 111, at index zero
    is the required one-Lipschitz trapezoid on
    [1/2,7/2], equal to one on [3/2,5/2]. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanOneNormDifferential
  InnerNorm HilbertFormCompactness IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_trapezoid_input]: the positive
    one-Lipschitz trapezoid used to prove the smooth
    cutoff existence in Federer 4.1.12, p. 369.
    It reuses the original interval bump of
    2.5.17, p. 111, before regularisation. *)
Definition current_trapezoid_input (R:realType) (x:R_n R 1%N):R^o:=
  @interval_bump R (1/2) (7/2) 0%N (euclidean_one_project x).

(** Source for [current_trapezoid_input_range]: values
    are in [0,1], supporting the cutoffs of
    Federer 4.1.12, p. 369. *)
Lemma current_trapezoid_input_range (R:realType) x:0<=@current_trapezoid_input R x<=1.
Proof.
apply/andP;split;[exact:interval_bump_ge0|exact:interval_bump_le1].
Qed.

(** Source for [current_trapezoid_input_lipschitz]: the
    original trapezoid has the exact Lipschitz constant
    one, supporting the printed derivative estimate in
    Federer 4.1.12, p. 369. *)
Lemma current_trapezoid_input_lipschitz (R:realType) (x y:R_n R 1%N):
  `|@current_trapezoid_input R x-@current_trapezoid_input R y|<=
    inner_norm (@euclidean_inner_productP R 1%N) (x-y).
Proof.
have h:=@interval_bump_lipschitz R (1/2) (7/2) 0%N (euclidean_one_project x) (euclidean_one_project y).
rewrite !mul1r in h.
rewrite euclidean_one_norm_coordinate /current_trapezoid_input !ffunE !mul1r.
exact:h.
Qed.

(** Source for [current_trapezoid_input_continuous]: the
    actual trapezoid meets the original continuous-input
    hypothesis of regularisation, supporting Federer
    4.1.12, p. 369, by 4.1.2, p. 347. *)
Lemma current_trapezoid_input_continuous (R:realType):
  norm_class_zero (inner_norm (@euclidean_inner_productP R 1%N))
    (fun t:R^o=>`|t|) (fun _=>True) (@current_trapezoid_input R).
Proof.
move=>x _;split;first exact:norm_full_domain_interior.
move=>epsilon hEpsilon;exists epsilon;split;first exact:hEpsilon.
move=>v _ hSmall.
have hBound:=@current_trapezoid_input_lipschitz R (x+v) x.
have hSub:(x+v)-x=v by rewrite (addrC x v) addrK.
rewrite hSub in hBound;exact:le_lt_trans hBound hSmall.
Qed.

(** Source for [current_trapezoid_input_plateau]: the
    actual input is one on [3/2,5/2],
    leaving the kernel margin needed to retain value
    one at 2 in Federer 4.1.12, p. 369. *)
Lemma current_trapezoid_input_plateau (R:realType) x:
  3/2<=euclidean_one_project x<=5/2->@current_trapezoid_input R x= 1.
Proof.
move=>/andP[h0 h1].
have hDistance:1<=Order.min (euclidean_one_project x-1/2) (7/2-euclidean_one_project x).
  rewrite le_min;apply/andP;split;lra.
rewrite /current_trapezoid_input /interval_bump !mul1r.
rewrite !mul1r in hDistance.
by rewrite minEle hDistance maxEle ler01.
Qed.

(** Source for [current_trapezoid_input_zero]: the
    actual input vanishes off (1/2,7/2), supporting
    the compact support of the smooth original cutoffs
    in Federer 4.1.12, p. 369. *)
Lemma current_trapezoid_input_zero (R:realType) x:
  ~~(1/2<euclidean_one_project x<7/2)->@current_trapezoid_input R x=0.
Proof. exact:(@interval_bump_zero R (1/2) (7/2) 0%N (euclidean_one_project x)). Qed.
