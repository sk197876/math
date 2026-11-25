(** Federer (1969), 4.1.3, p. 348: the displayed product
    of one common one-variable test is an actual regularising
    kernel when its support is small enough. The exact integral
    is the registered finite-coordinate Fubini theorem of 2.6.4.
    Dimension zero retains the empty product and unit point mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation TestCoordinateProductSmooth
  EuclideanCoordinateLoneBound CompactSupportFunctionUP SmoothingKernelUP
  EuclideanFiniteProductIntegral EuclideanLebesgueDimensions LebesgueScalarMeasure
  MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SeparatedSmoothingKernel.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable A:lmodType R.
Variable av:A->R^o->R^o.
Hypothesis hA:is_smooth_function_space hR hR (fun _=>True) av.
Variable gamma:smooth_test_space hA.
Variable r:R.
Hypothesis hr:0<=r.
Hypothesis hSmall:n%:R*r<1.
Hypothesis hNonnegative:forall t:R,0<=smooth_test_value hA gamma t.
Hypothesis hSupport:forall t:R,smooth_test_value hA gamma t<>0 ->`|t|<=r.
Hypothesis hIntegral:is_measure_integral (@lebesgue_scalar_measure R)
  (real_total_integrand (smooth_test_value hA gamma)) (1:R)%:E.
Local Notation phi := (fun x:X=>\prod_i smooth_test_value hA gamma (x i)).
Local Notation C := ([set x:real_norm_metric_space hN|N x<=n%:R*r]).

(** Source for [separated_smoothing_kernel_laws]: the original
    separated product is nonnegative, smooth, normalized and
    supported strictly inside the Euclidean unit ball, Federer
    4.1.3, p. 348, with the requirements of 4.1.2, p. 346. *)
Theorem separated_smoothing_kernel_laws:is_smoothing_kernel phi.
Proof.
have hCompact:compact C.
  have h:=@finite_norm_closed_ball_compact R X n (@coordinate_basis R n)
    (@coordinate_basisP R n) N hN 0 (n%:R*r).
  have hEq:[set x:real_norm_metric_space hN|N (x-0)<=n%:R*r]=C.
    apply:funext=>x.
    change (is_true (N (x-0)<=n%:R*r)=is_true (N x<=n%:R*r)).
    by rewrite subr0.
  by rewrite hEq in h.
have hClosed:closed C:=compact_closed (@metric_hausdorff R (real_norm_metric_space hN)) hCompact.
have hOff x:~C x ->phi x=0.
  move=>hx; case:(eqVneq (phi x) 0)=>[hZero|hn]; first exact hZero.
  exfalso.
  have hEach i:smooth_test_value hA gamma (x i)<>0.
    move=>hZero.
    have hP:phi x=0 by rewrite (bigD1 i) //= hZero mul0r.
    by move:hn; rewrite hP eqxx.
  have hBound:N x<=n%:R*r.
    apply:le_trans (euclidean_coordinate_lone_bound x) _.
    have hSum:(\sum_i `|x i|)<=\sum_(i:'I_n) r.
      apply:ler_sum=>i _; exact:hSupport (hEach i).
    by rewrite sumr_const card_ord -mulr_natl in hSum.
  exact:hx hBound.
constructor.
- exact:(@test_coordinate_product_smooth R n A av hA (fun _=>gamma)).
- move=>x; apply:prodr_ge0=>i _; exact:hNonnegative.
- exact:(@real_function_compact_support_in_closed_set R (real_norm_metric_space hN) phi C
    hCompact hClosed hOff).
- have hSub:=@real_function_support_in_closed_set R (real_norm_metric_space hN) phi C hClosed hOff.
  move=>x hx; exact:le_lt_trans (hSub x hx) hSmall.
- have h:=@euclidean_finite_product_integral R n
    (fun _=>smooth_test_value hA gamma) (fun _=>1) (fun _=>hIntegral).
  have hOne:(\prod_(i:'I_n) (1:R))= 1 by apply:big1.
  by rewrite hOne in h.
Qed.
End SeparatedSmoothingKernel.
