(** Federer (1969), 3.1.11, p. 219:
    the exact second-differential graph supplies the
    quadratic second-difference remainder. No continuity
    of the second derivative in a neighbourhood is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormClassOneNormalization NormOperatorNormUP ContinuousOperatorUP
  ContinuousMultilinearUP ContinuousMultilinearOne
  MultilinearSuccessorArguments NormHigherDifferentialUP NormHigherDifferentialFirst
  NormSecondDifferenceUP NormSecondDifferenceEstimate NormSecondDifferenceSymmetry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SecondDerivative.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).
Variable A : set X.
Variable f : X->Y.
Variable a : X.
Variable z : Z 2%N.
Local Notation HD := (@has_norm_higher_differential R X Y NX Z evaluation ZN A f).

(** Source for [norm_second_differential_remainder]:
    twice differentiability at a implies the second-difference
    limit, Federer 3.1.11, p. 219. The represented
    bilinear form has the printed order of its two arguments. *)
Theorem norm_second_differential_remainder :
  HD 2%N a z ->
  exists B : Hom X (Hom X Y),
    (forall u v, B v u=
      @evaluation 2%N (multilinear_successor_arguments [ffun i : 'I_1=>u] v) z) /\
    has_norm_quadratic_second_remainder NX NY f a B.
Proof.
move=> [g [hg [L [hL heL]]]].
pose J := @continuous_multilinear_one_evaluation R X Y (Z 1%N) NX NY
  (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N).
have hJ := @continuous_multilinear_one_operator_space R X Y (Z 1%N) NX NY
  (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N).
pose B := hom_comp J L.
have hBe u v : B v u=
    @evaluation 2%N (multilinear_successor_arguments [ffun i : 'I_1=>u] v) z.
  rewrite /B hom_compE.
  change (@evaluation 1%N [ffun i : 'I_1=>u] (L v)=
    @evaluation 2%N (multilinear_successor_arguments [ffun i : 'I_1=>u] v) z).
  exact: heL.
exists B; split=> // e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [rho [hrho hdomain]] := norm_differential_interior hL.
have [d [hd herror]] := norm_differential_remainder hL he2.
pose r := Num.min rho d / 3.
have hmin : 0<Num.min rho d by rewrite lt_min hrho hd.
have hr : 0<r by rewrite /r divr_gt0 // ltr0n.
have hrr : 2*r<rho.
  have hm : Num.min rho d<=rho by rewrite ge_min lexx.
  rewrite /r; lra.
have hrd : 2*r<d.
  have hm : Num.min rho d<=d by rewrite ge_min lexx orbT.
  rewrite /r; lra.
pose D x := J (g (a+x)).
pose F x := f (a+x)-f a.
pose A0 := [set x | A (a+x)].
have hga x : NX x< 2*r -> HD 1%N (a+x) (g (a+x)).
  move=> hx; have [w hw] := hdomain x (lt_trans hx hrr).
  by rewrite (hg _ _ hw).
have hDf x : NX x< 2*r -> has_norm_differential NX NY A0 F x (D x).
  move=> hx.
  have hdx := (@norm_higher_differential_first R X Y NX NY hNX hNY
    Z evaluation ZN hZ A f (a+x) (g (a+x))).1 (hga x hx).
  exact: (@norm_differential_translate R X Y NX NY A f a x (f a) (D x) hdx).
have hDr x : NX x< 2*r -> forall w,
    NY ((D x-D 0-B x) w)<=(e/2)*NX x*NX w.
  move=> hx w.
  have hh := herror x (hdomain x (lt_trans hx hrr)) (lt_trans hx hrd).
  have hnorm := norm_operator_bound (continuous_operator_norm_laws hJ
    (g (a+x)-g a-L x)) w.
  have hid : D x-D 0-B x=J (g (a+x)-g a-L x).
    by rewrite /D /B hom_compE addr0 !linearB.
  rewrite hid; apply: le_trans hnorm _.
  have hmul := ler_wpM2r (real_seminorm_nonnegative hNX.1 w) hh.
  exact hmul.
have hB v : norm_bounded_linear NX NY (B v).
  exact: continuous_operator_bounded hJ (L v).
exists r; split=> // u v hu hv.
have hh := @norm_second_difference_estimate R X Y NX NY hNX hNY A0 F D B
  (e/2) r (ltW he2) hr hDf hDr hB u v hu hv.
rewrite /F norm_second_difference_translate in hh.
have heq : 2*(e/2)=e by lra.
by rewrite heq in hh.
Qed.

(** Source for [norm_second_differential_symmetric]:
    the corollary that D^2 f(a) is a symmetric bilinear
    form, Federer 3.1.11, p. 219. It follows from
    the proved four-point estimate, without assuming symmetry
    in the multilinear-space interface. *)
Theorem norm_second_differential_symmetric :
  HD 2%N a z -> forall u v,
    @evaluation 2%N (multilinear_successor_arguments [ffun i : 'I_1=>u] v) z=
    @evaluation 2%N (multilinear_successor_arguments [ffun i : 'I_1=>v] u) z.
Proof.
move=> hz u v; have [B [he hb]] := norm_second_differential_remainder hz.
rewrite -!he.
have hs := norm_quadratic_second_remainder_symmetric hNX hNY hb u v.
exact hs.
Qed.
End SecondDerivative.
