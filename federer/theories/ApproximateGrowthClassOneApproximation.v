(** Federer (1969), 3.1.16, p. 228: Lusin approximation by a map of
    class one under finite approximate upper growth almost everywhere.
    Follow 3.1.8, compact annular restrictions, the successive sealed
    Lipschitz extensions of 2.10.43, and 3.1.15 with k=0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness ContinuousMultilinearUP
  NormHigherDifferentialUP NormClassHigherUP NormClassHigherLaws
  EuclideanLebesgueDimensions MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP
  LipschitzUP CenteredBallRelations ApproximateMetricGrowth MeasureApproximateOrderLimits
  ApproximateGrowthNullRestriction ApproximateGrowthAnnularPieces
  AnnularLipschitzExtensionUP AnnularLipschitzExtensionSealed AnnularLipschitzExtensionLaws
  LusinClassApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_1_16_positive]: Federer 3.1.16, p. 228, with
    positive source dimension and arbitrary finite target dimension.
    The null exceptional set is removed explicitly; A need not be
    measurable, and undefined quotient inputs remain exceptional. *)
Theorem federer_3_1_16_positive (R : realType) m n
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m.+1))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (A : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (f : inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m.+1) A
    [set a | (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m.+1)
      (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
      (partial_metric_growth_quotient A f a) a< +oo)%E] ->
  forall e : R, 0<e -> exists g,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m.+1))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g 1%N /\
    (@euclidean_lebesgue_measure R m.+1 (A `\` [set x | f x=g x])<e%:E)%E.
Proof.
move=>hae e he.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose NX := inner_norm (@euclidean_inner_productP R m.+1).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose hm := euclidean_lebesgue_is_measure R m.+1.
pose P := [set a : X | (measure_approximate_upper_limit mu
  (@centered_closed_ball_relation R [the metricType R of X])
  (partial_metric_growth_quotient A f a) a< +oo)%E].
pose Bad := A `\` P.
pose A0 := A `\` Bad.
have hBad : mu Bad=0%E := hae.
have hgrowth a : A0 a -> (measure_approximate_upper_limit mu
    (@centered_closed_ball_relation R [the metricType R of X])
    (partial_metric_growth_quotient A0 f a) a< +oo)%E.
  move=>[ha hn].
  have hp : P a by apply: contrapT=>hbad; apply: hn; split.
  exact (finite_approximate_growth_null_restriction hBad hp).
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [C [hC herror]] := finite_approximate_growth_annular_compacts hgrowth he2.
have hCc i : compact (C i) := (hC i).1.
have hCU i : C i `<=` OpenAnnuliClosedUnion.open_annulus (0:X) i.
  by move=>x hx; exact ((hC i).2.1 x hx).2.
have hCL i : is_metric_lipschitz (C i) f := (hC i).2.2.
pose h := @AnnularLipschitzExtension.value R m.+1 n C f hCc hCU hCL.
have hh := @AnnularLipschitzExtension.laws R m.+1 n C f hCc hCU hCL.
have hherror : (mu (A `\` [set x | f x=h x])<(e/2)%:E)%E.
  have hcov : A `\` [set x | f x=h x] `<=` Bad `|` (A0 `\` \bigcup_i C i).
    move=>x [ha hn]; case: (pselect (Bad x))=>[hx|hx]; first by left.
    right; split; first by split.
    move=>[i _ hi]; apply: hn; exact: esym (annular_extension_agreement hh hi).
  have hb := @measure_binary_cover R X mu hm _ Bad _ hcov.
  rewrite hBad add0e in hb.
  exact: le_lt_trans hb herror.
have hh0 := annular_extension_class_zero hh.
have hclass0 : norm_class_higher NX NY ev ZN (fun _=>True) h 0%N.
  exact ((@norm_class_higher_zero R (R_n R m.+1) (R_n R n) NX NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) Z ev ZN hZ (fun _=>True) h).2 hh0).
have hbound a : True -> forall z, has_norm_higher_differential NX ev ZN (fun _=>True) h 0%N a z ->
    exists M r : R, 0<r /\ forall x w, True ->
      has_norm_higher_differential NX ev ZN (fun _=>True) h 0%N x w ->
      NX (x-a)<r -> @ZN 0%N (w-z)<=M*NX (x-a).
  move=>_ z hz.
  have [M [r [hr hb]]] := @annular_extension_zeroth_growth R m.+1 n C f h hh Z ev ZN hZ a z hz.
  by exists M, r; split=>// x w _; exact: hb x w.
have [g [hg hge]] := @federer_3_1_15 R m.+1 n Z ev ZN hZ 0%N setT setT h
  hclass0 (fun x hx=>hx) hbound (e/2) he2.
exists g; split; first exact hg.
have hcov : A `\` [set x | f x=g x] `<=`
    (A `\` [set x | f x=h x]) `|` (setT `\` [set x | h x=g x]).
  move=>x [ha hn]; case: (pselect (f x=h x))=>[hfh|hfh]; last by left; split.
  right; split; first exact I.
  by move=>hhg; exact (hn (eq_trans hfh hhg)).
have hb := measure_binary_cover hm hcov.
have hs := lteD hherror hge.
rewrite -EFinD in hs.
have hhalf : e/2+e/2=e by lra.
rewrite hhalf in hs.
exact: le_lt_trans hb hs.
Qed.

(** Source for [federer_3_1_16]: the complete theorem of Federer
    3.1.16, p. 228, including a zero-dimensional source.
    The base variable a follows erratum p. 4, book p. 228 line 19.
    For every positive tolerance a global map of class one agrees with f except
    on a subset of A of smaller Lebesgue measure. *)
Theorem federer_3_1_16 (R : realType) m n
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (@ev i) (@ZN i))
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) A
    [set a | (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m)
      (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
      (partial_metric_growth_quotient A f a) a< +oo)%E] ->
  forall e : R, 0<e -> exists g,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g 1%N /\
    (@euclidean_lebesgue_measure R m (A `\` [set x | f x=g x])<e%:E)%E.
Proof.
case: m Z ev ZN hZ A f=>[|m] Z ev ZN hZ A f hg e he.
- exact: (@federer_3_1_15_zero R n Z ev ZN hZ 0%N A f e he).
- exact: (@federer_3_1_16_positive R m n Z ev ZN hZ A f hg e he).
Qed.
