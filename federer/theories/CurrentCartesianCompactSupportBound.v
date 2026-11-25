(** Federer (1969), 4.1.8, p. 360, used in
    4.1.12, p. 369: supported factors give the
    exact compact product support bound. Reuse the
    original product support theorem without a mass
    or normality hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianSupportUpper SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianCompactSupportBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables (KA:smooth_compact_set hNX A) (KB:smooth_compact_set hNY B)
  (KAB:smooth_compact_set hNZ AB).
Hypothesis hKAB:smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
(** Source for [current_cartesian_compact_support_bound]:
    supported factors give support in their exact
    compact product, supporting Federer 4.1.12,
    p. 369, by 4.1.8, p. 360. No
    finite mass or normality premise is needed. *)
Theorem current_cartesian_compact_support_bound
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  @current_support R h2 m A hA i S `<=` smooth_compact_carrier KA->
  @current_support R h2 n B hB j T `<=` smooth_compact_carrier KB->
  @current_support R h2 (m+n) AB hAB (i+j)
    (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T) `<=` smooth_compact_carrier KAB.
Proof.
move=>hSupportS hSupportT z hz;rewrite hKAB.
have hFactors:=@current_cartesian_support_upper R h2 m n i j A B hA hB S T z hz.
split;[exact:hSupportS _ hFactors.1|exact:hSupportT _ hFactors.2].
Qed.
End CurrentCartesianCompactSupportBound.
