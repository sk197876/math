(** Federer (1969), 4.1.24, pp. 380–381: enlarging
    an original compact index preserves every approximation
    and decomposition property. These exact inclusions justify
    use of the full compact unions; no exhaustion or
    support-only replacement of the classes is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces RectifiableCurrentApproximationUP
  IntegralCurrentClassesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralCurrentMonotone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(fun m=>@current_space R h2 n U hU m).
Variables K L:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Hypothesis hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L.

(** Source for [rectifiable_image_approximant_monotone]: the
    original f(C) inclusion is preserved by K contained
    in L, supporting the unions of 4.1.24, p. 381. *)
Theorem rectifiable_image_approximant_monotone m (Q:C m):
  @is_rectifiable_image_approximant R h2 n m U hU K Q->
  @is_rectifiable_image_approximant R h2 n m U hU L Q.
Proof.
move=>[d [Z [hZ [A [f [hImage [hLip [P [hP [hAK hValue]]]]]]]]]].
exists d,Z,hZ,A,f,hImage,hLip,P,hP;split;last exact:hValue.
move=>x hx;exact:hKL (f x) (hAK x hx).
Qed.

(** Source for [rectifiable_current_compact_monotone]: the
    literal original mass approximation retains its witnesses
    after enlarging the compact index, 4.1.24, pp. 380–381. *)
Theorem rectifiable_current_compact_monotone m (T:C m):
  @is_rectifiable_current_supported_in R h2 n m U hU K T->
  @is_rectifiable_current_supported_in R h2 n m U hU L T.
Proof.
move=>hT epsilon hEpsilon;have[Q [hQ hError]]:=hT epsilon hEpsilon.
exists Q;split;last exact:hError.
exact:rectifiable_image_approximant_monotone hQ.
Qed.

(** Source for [integral_current_compact_monotone]: both
    original rectifiable conditions of I_(m,K), and the
    degree-zero clause, are preserved under K contained
    in L, Federer 4.1.24, p. 381. *)
Theorem integral_current_compact_monotone m (T:C m):
  @is_integral_current_supported_in R h2 n U hU m K T->
  @is_integral_current_supported_in R h2 n U hU m L T.
Proof.
case:m T=>[|j] T hT;first exact:rectifiable_current_compact_monotone hT.
split.
- exact:rectifiable_current_compact_monotone hT.1.
- exact:rectifiable_current_compact_monotone hT.2.
Qed.

(** Source for [integral_flat_current_compact_monotone]: the
    same original rectifiable decomposition witnesses membership
    after enlarging K, supporting the integral-flat union
    in Federer 4.1.24, p. 381. *)
Theorem integral_flat_current_compact_monotone m (T:C m):
  @is_integral_flat_current_supported_in R h2 n U hU m K T->
  @is_integral_flat_current_supported_in R h2 n U hU m L T.
Proof.
move=>[A [S [hA [hS hEqual]]]];exists A,S;split.
- exact:rectifiable_current_compact_monotone hA.
- split;last exact:hEqual.
  exact:rectifiable_current_compact_monotone hS.
Qed.
End IntegralCurrentMonotone.
