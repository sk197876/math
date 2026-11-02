(** Federer (1969), 3.1.4, pp. 215–216: off the exceptional
    coordinate sets, telescope the scalar increments and bound their
    total remainder by (2m/j)|v|. These supporting inequalities do not
    assume any measure-theoretic differentiability conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm EuclideanCoordinateMetric EuclideanCoordinateStaircase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coordinate_remainder_telescope_bound]: the last
    displayed inequality in Federer 3.1.4, p. 216. The error parameter
    is a nonnegative real number; taking epsilon=1/j gives the printed
    estimate. Empty coordinate families are included. *)
Lemma coordinate_remainder_telescope_bound (R : realType) n
    (f : R_n R n -> R) (a h : R_n R n) (g : 'I_n -> R) (e : R) :
  0<=e ->
  (forall i : 'I_n,
    `|f (a+coordinate_prefix h i.+1)-f (a+coordinate_prefix h i)-h i*g i|<=2*e*`|h i|) ->
  `|f (a+h)-f a-\sum_(i<n) h i*g i|<=
    (2*n%:R*e)*inner_norm (@euclidean_inner_productP R n) h.
Proof.
move=> he hs.
rewrite (coordinate_staircase_telescope f a h) -sumrB.
apply: le_trans (ler_norm_sum _ _ _) _.
have hcoef : 0<=2*e by rewrite mulr_ge0 // ler0n.
apply: le_trans (_ : \sum_(i<n) `|f (a+coordinate_prefix h i.+1)-f (a+coordinate_prefix h i)-h i*g i|
    <=\sum_(i<n) (2*e*inner_norm (@euclidean_inner_productP R n) h)) _.
- apply: ler_sum=> i _; apply: le_trans (hs i) _.
  exact (ler_wpM2l hcoef (@euclidean_coordinate_norm_bound R n i h)).
- rewrite sumr_const card_ord -[(_ *+ n)]mulr_natr.
  have heq : (2*e*inner_norm (@euclidean_inner_productP R n) h)*n%:R=
      (2*n%:R*e)*inner_norm (@euclidean_inner_productP R n) h by ring.
  by rewrite heq.
Qed.

(** Source for [coordinate_staircase_approximation_bound]: combine
    the two terms on p. 215, final display, then telescope as on p. 216
    in Federer 3.1.4. The variation bound is supplied by avoiding the
    exceptional set with the erratum's corrected threshold >=1/j
    (erratum, book p. 214 line 24). *)
Theorem coordinate_staircase_approximation_bound (R : realType) n
    (f : R_n R n -> R) (g : 'I_n -> R_n R n -> R)
    (a h : R_n R n) (e : R) :
  0<=e ->
  (forall i : 'I_n, let x:=a+coordinate_prefix h i in
    `|f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i x|<=e*`|h i|) ->
  (forall i : 'I_n, `|g i (a+coordinate_prefix h i)-g i a|<=e) ->
  `|f (a+h)-f a-\sum_(i<n) h i*g i a|<=
    (2*n%:R*e)*inner_norm (@euclidean_inner_productP R n) h.
Proof.
move=> he hs hv; apply: (coordinate_remainder_telescope_bound he)=> i.
pose x:=a+coordinate_prefix h i.
have hi := hs i; change (is_true (`|f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i x|<=e*`|h i|)) in hi.
have hvi := hv i.
rewrite coordinate_prefix_step addrA.
change (is_true (`|f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i a|<=2*e*`|h i|)).
have hid : f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i a=
    (f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i x)+h i*(g i x-g i a) by ring.
rewrite hid; apply: le_trans (ler_normD _ _) _.
have hm := ler_wpM2l (normr_ge0 (h i)) hvi.
rewrite normrM; change (is_true (`|h i|*`|g i x-g i a|<=`|h i|*e)) in hm.
lra.
Qed.
