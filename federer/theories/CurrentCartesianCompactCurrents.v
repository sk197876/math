(** Federer (1969), 4.1.11, p. 364: compact current factors
    make the Cartesian product used in the join compact. Reuse the
    exact original support equality of 4.1.8, p. 360, and the
    preceding compact Cartesian-product theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianSupportEquality CurrentCartesianCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_cartesian_compact_currents]: the original
    product of compactly supported currents has compact support,
    supporting the join definition in Federer 4.1.11, p. 364.
    No integration representation or global-domain premise is added. *)
Theorem current_cartesian_compact_currents
    (R : realType) (h2 : (1+1:R)!=0) (m n i j : nat)
    (A : set (R_n R m)) (B : set (R_n R n))
    (hA : forall x, A x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A x)
    (hB : forall y, B y -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B y)
    (S : @current_space R h2 m A hA i)
    (T : @current_space R h2 n B hB j) :
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m A hA i S) ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n B hB j T) ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (m+n))))
      (@current_support R h2 (m+n)
        (@euclidean_cartesian_set R m n A B)
        (@current_cartesian_domain_open R m n A B hA hB) (i+j)
        (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T)).
Proof.
move=> hS hT.
rewrite (@current_cartesian_support R h2 m n i j A B hA hB S T).
exact: (@current_cartesian_compact R m n
  (@current_support R h2 m A hA i S)
  (@current_support R h2 n B hB j T) hS hT).
Qed.
