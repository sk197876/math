(** Federer (1969), 3.4.2(7), p. 313: a finite derivative
    expansion bounds ζ by the function oscillation bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP PartialFunctionUP RelativeDifferential ExtendedSupremumUP
  RealPower CriticalOscillationUP CriticalOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_eta_increment_upper_bound]: the individual
    function increments in the finite sum of 3.4.2(7), p. 313.
    The public supremum laws give the bound from any finite upper
    bound for η, retaining every original positive-distance test. *)
Lemma critical_eta_increment_upper_bound (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (T G:set (R_n R m))
    (f:R_n R m->Y) lambda delta b x c:
  (critical_eta NY Z T G f lambda delta<=b%:E)%E ->T x ->G c ->Z (x-c) ->
  0<inner_norm (@euclidean_inner_productP R m) (x-c)<=delta ->
  NY (f x-f c)<=b*real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda.
Proof.
move=>hBound hx hc hZ hDist.
have hTest:critical_function_oscillation_values NY Z T G f lambda delta
    (NY (f x-f c)/real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda).
  right;exists x,c;by repeat split.
have hUpper:=extended_supremum_upper (critical_eta_laws NY Z T G f lambda delta) hTest.
have h:=le_trans hUpper hBound.
rewrite lee_fin (ler_pdivrMr _ _ (@real_power_strictly_positive R _ lambda (andP hDist).1)) in h.
exact:h.
Qed.

(** Source for [critical_finite_derivative_oscillation_bound]: the
    inequality ζ<=sum η in the proof of 3.4.2(7), p. 313,
    expressed with arbitrary finite upper bounds for the summands.
    Unit-vector coefficients have absolute value at most one.
    Every derivative value is the genuine relative derivative on T. *)
Theorem critical_finite_derivative_oscillation_bound (R:realType) m
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (T G:set (R_n R m)) (f:R_n R m->Y)
    (I:finType) (e:I->R_n R m) (fi:I->R_n R m->Y) (b:I->R) lambda delta:
  (forall i,0<=b i) ->(forall i c,G c ->fi i c=0) ->
  (forall z,Z z ->inner_norm (@euclidean_inner_productP R m) z<=1 ->
    exists a:I->R,(forall i,`|a i|<=1) /\z=\sum_i a i*:e i) ->
  (forall x,T x ->forall (L:partial_function (R_n R m) Y) z y (a:I->R),
    partial_function_graph (relative_norm_differential
      (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY T T f) x L ->
    partial_function_graph L z y ->z=\sum_i a i*:e i ->y=\sum_i a i*:fi i x) ->
  (forall i,(critical_eta NY Z T G (fi i) lambda delta<=(b i)%:E)%E) ->
  (critical_zeta hNY Z T G f lambda delta<=(\sum_i b i)%:E)%E.
Proof.
move=>hb hZero hCoordinates hFormula hEta.
apply:(extended_supremum_least (critical_zeta_laws hNY Z T G f lambda delta)).
move=>q [->|[x [c [z [L [y hData]]]]]].
- rewrite lee_fin;apply:sumr_ge0=>i _;exact:hb.
- have [hx [hc [hZ [hDist [hz [hUnit [hOuter [hInner ->]]]]]]]]:=hData.
  pose P:=real_power (inner_norm (@euclidean_inner_productP R m) (x-c)) lambda.
  have hP:0<P:=@real_power_strictly_positive R _ lambda (andP hDist).1.
  rewrite lee_fin (ler_pdivrMr _ _ hP).
  have [a [hUnitCoordinates hExpansion]]:=hCoordinates z hz hUnit.
  have hValue:=hFormula x hx L z y a hOuter hInner hExpansion.
  rewrite hValue.
  apply:(le_trans (real_seminorm_sum hNY.1 _)).
  have hEach i:NY (a i*:fi i x)<=b i*P.
    rewrite (real_seminorm_scale hNY.1).
    have hFunction:=@critical_eta_increment_upper_bound R m Y NY Z T G (fi i)
      lambda delta (b i) x c (hEta i) hx hc hZ hDist.
    rewrite (hZero i c hc) subr0 in hFunction.
    have hFirst:=ler_wpM2r (real_seminorm_nonnegative hNY.1 (fi i x)) (hUnitCoordinates i).
    rewrite mul1r in hFirst.
    exact:(le_trans hFirst hFunction).
  have hSum:(\sum_i NY (a i*:fi i x))<=\sum_i b i*P.
    apply:ler_sum=>i _;exact:hEach.
  by rewrite -big_distrl in hSum.
Qed.
