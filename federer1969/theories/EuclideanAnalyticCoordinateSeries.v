(** Federer (1969), 3.1.24, pp. 240–241: the
    Euclidean coordinate series has the actual multiindex partial
    derivatives as coefficients and converges absolutely. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness EuclideanCoordinateMetric EuclideanCoordinateTopology RealNormUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherMultiPartialUP
  SymmetricForms SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials
  SymmetricMonomialTuples NormAnalyticUP NormAnalyticCoordinateSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_analytic_coordinate_series]: the
    coordinate partial-derivative expansion in Federer 3.1.24,
    pp. 240–241. The coefficient for alpha is the
    actual D^alpha f(a) of 3.1.11, p. 223.
    The sum of absolute coordinate increments is small enough
    to stay inside the original domain. Both convergence to
    f and absolute convergence are proved, including dimension
    zero and an unrestricted constant coefficient. *)
Theorem euclidean_analytic_coordinate_series (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R n)) (f:R_n R n->Y) (a:R_n R n) :
  @norm_analytic_at R (R_n R n) Y _ NY
    (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A f a ->
  exists (C:R) (P:forall m,symmetric_indices n m->Y),0<C /\
    (forall m b,has_norm_multi_partial (inner_norm (@euclidean_inner_productP R n))
      (fun i=>@ContinuousMultilinear.evaluation R i (R_n R n) Y _ NY
        (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY)
      (fun i=>@ContinuousMultilinear.norm R i (R_n R n) Y _ NY
        (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY) A f b a (P m b)) /\
    forall x:R_n R n,\sum_i `|x i-a i|<C^-1 -> A x /\
      (forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N ->
        NY (f x-\sum_(m<N.+1) \sum_(b:symmetric_indices n m)
          (symmetric_scalar_monomial (fun i=>x i-a i) (symmetric_indices_unbound b)/
            (symmetric_multi_factorial (symmetric_indices_unbound b))%:R)*:P m b)<eps) /\
      exists B:R,forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N ->
        `|(\sum_(m<N) \sum_(b:symmetric_indices n m)
          `|symmetric_scalar_monomial (fun i=>x i-a i) (symmetric_indices_unbound b)/
            (symmetric_multi_factorial (symmetric_indices_unbound b))%:R|*NY (P m b))-B|<eps.
Proof.
move=>hf.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hv i:NX (@coordinate_basis R n i)<=1 by rewrite /NX euclidean_coordinate_unit_norm.
have [C [phi [hC [hActual [hBound hSeries]]]]]:=
  @norm_analytic_coordinate_series R (R_n R n) Y NX NY hNX hNY A f a n (@coordinate_basis R n) hv hf.
pose P m (b:symmetric_indices n m):=phi m (symmetric_monomial_tuple (@coordinate_basis R n) b).
exists C,P; split; first exact hC.
split.
- move=>m b.
  have hh:=norm_multi_partial_form_evaluation b (hActual m).
  by rewrite SymmetricMonomialTuples.symmetric_monomial_form_value in hh.
- move=>x hx.
  pose t:=fun i:'I_n=>x i-a i.
  have hShift:a+\sum_i t i*:(@coordinate_basis R n i)= x.
    have hh:=@euclidean_coordinate_expansion R n (x-a).
    have he:(\sum_i t i*:(@coordinate_basis R n i))= x-a.
      rewrite -hh; apply:eq_bigr=>i _; by rewrite /t !ffunE.
    by rewrite he addrC subrK.
  have hh:=hSeries t hx.
  by rewrite hShift in hh.
Qed.
