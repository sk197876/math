(** Federer (1969), 3.1.15, p. 227:
    "Assured by 3.1.9 that L^m(A-dmn D D^k f)=0". The coordinate
    functions D^alpha f=ev(e^alpha) o D^k f of the top differential
    inherit the finite upper growth hypothesis, so Stepanoff's
    theorem makes each of them differentiable at almost every
    point of A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  EuclideanLebesgueDimensions MetricSlopeLimsup ExtendedRealBounds
  NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  SymmetricMultiIndices NormHigherMultiPartialUP MeasureUP MeasureAlmostUP MeasureAlmostBasic Stepanoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section TopDifferentialStepanoff.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Yn := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variables (A B : set X).
Variable f : X->R_n R n.
Hypothesis hAB : A `<=` B.
Hypothesis hB : open B.
Variable Dk : X->Z k.
Hypothesis hgrowth : forall a, A a -> exists M r : R, 0<r /\
  forall x, B x -> N (x-a)<r -> @ZN k (Dk x-Dk a)<=M*N (x-a).

(** Source for [top_coordinate]:
    the multi-partial D^alpha f=D^k f(e^alpha) of order k,
    Federer 3.1.11, p. 223, as a coordinate of the top
    differential in 3.1.15, p. 227. *)
Definition top_coordinate (alpha : symmetric_indices m k) (x : X) : Yn :=
  @ev k (norm_multi_partial_arguments R alpha) (Dk x).

(** Source for [top_coordinate_increment]:
    the increments of a coordinate are bounded by those of the
    top differential, Federer 3.1.11, p. 219, operator norm. *)
Lemma top_coordinate_increment (alpha : symmetric_indices m k) (x y : X) :
  NY (top_coordinate alpha x-top_coordinate alpha y)<=
    @ZN k (Dk x-Dk y)*\prod_(i<k) N (norm_multi_partial_arguments R alpha i).
Proof.
rewrite /top_coordinate -raddfB.
exact: (multilinear_operator_bound (continuous_multilinear_norm_laws (@hZ k) (Dk x-Dk y))
  (norm_multi_partial_arguments R alpha)).
Qed.

(** Source for [top_coordinate_growth]:
    the hypothesis limsup ||D^k f(x)-D^k f(a)||/|x-a|<infinity of
    Federer 3.1.15, p. 227, passes to every coordinate. *)
Lemma top_coordinate_growth (alpha : symmetric_indices m k) (a : X) : A a ->
  (metric_local_slope_limsup B (top_coordinate alpha) a< +oo)%E.
Proof.
move=>ha; have [M [r [hr hM]]] := hgrowth ha.
set C := \prod_(i<k) N (norm_multi_partial_arguments R alpha i).
have hC : 0<=C by apply: prodr_ge0=>i _; exact: (real_seminorm_nonnegative hN.1).
apply: (le_lt_trans (y:=(Num.max M 0*C)%:E)); last exact: ltry.
apply: (le_trans (extended_real_inf_lower (S:=[set q | exists d : R, 0<d /\
  q=metric_slope_neighborhood_sup B (top_coordinate alpha) a d]) (x:=
  metric_slope_neighborhood_sup B (top_coordinate alpha) a r) _)).
  by exists r.
apply: extended_real_sup_least=>q [y [hy [/andP [hp hdy] ->]]].
rewrite lee_fin ler_pdivrMr //.
rewrite !inner_metric_distanceE in hp hdy *.
apply: (le_trans (top_coordinate_increment alpha a y)).
have hya : N (y-a)<r by rewrite (real_seminorm_subtract hN.1).
have hZ1 := hM y hy hya.
have hZN := continuous_multilinear_norm_is_norm hNY (@hZ k).
rewrite (real_seminorm_subtract hZN.1 (Dk a) (Dk y)) (real_seminorm_subtract hN.1 a y).
have hN0 := real_seminorm_nonnegative hN.1 (y-a).
have hMle : M<=Num.max M 0 by rewrite le_max lexx.
apply: (le_trans (ler_wpM2r hC hZ1)).
rewrite [Num.max M 0*C*N (y-a)]mulrAC.
exact: (ler_wpM2r hC (ler_wpM2r hN0 hMle)).
Qed.

(** Source for [top_coordinates_differentiable_almost_everywhere]:
    L^m(A-dmn D D^k f)=0 by Stepanoff's theorem 3.1.9, Federer
    3.1.15, p. 227, applied to the finitely many coordinates. *)
Theorem top_coordinates_differentiable_almost_everywhere :
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | forall alpha : symmetric_indices m k,
      norm_differentiable_at N NY B (top_coordinate alpha) a].
Proof.
have hm := euclidean_lebesgue_is_measure R m.
apply: (measure_almost_everywhere_on_implication _ _ _).2.
have hall : measure_almost_everywhere (@euclidean_lebesgue_measure R m)
    (\bigcap_(alpha in [set: symmetric_indices m k])
      [set x | A x -> norm_differentiable_at N NY B (top_coordinate alpha) x]).
  apply: (measure_almost_everywhere_countable hm); first exact: countableP.
  move=>alpha _; apply: (measure_almost_everywhere_on_implication _ _ _).1.
  exact: (federer_3_1_9 hAB hB (fun a ha=>top_coordinate_growth alpha ha)).
apply: (measure_almost_everywhere_mono hm _ hall)=>x hx ha alpha.
exact: (hx alpha I ha).
Qed.
End TopDifferentialStepanoff.
