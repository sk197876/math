(** Federer (1969), 4.1.18, pp. 374–375: on
    the whole Euclidean domain the original current
    support is ambient closed, even for arbitrary
    nonrepresented currents. Reuse relative support closedness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms CurrentSpaces FunctionalSupportRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_whole_support_closed]: the closed
    original support in the smoothing homotopy and
    support-tube assertions of Federer 4.1.18,
    pp. 374–375, from 4.1.1. *)
Theorem current_whole_support_closed (R:realType) (h2:(1+1:R)!=0)
    (n m:nat)
    (hU:forall x:R_n R n,True->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) (fun _=>True) x)
    (T:@current_space R h2 n (fun _=>True) hU m):
  @closed (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n (fun _=>True) hU m T).
Proof.
have [C [hClosed hEqual]]:=@functional_support_relative_closed R (R_n R n)
  (A_m (R_n R n) R^o m) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (fun _=>True)
  (@current_test_space R h2 n (fun _=>True) hU m)
  (@current_test_value R h2 n (fun _=>True) hU m)
  (@current_value R h2 n (fun _=>True) hU m T).
have hSupport:@current_support R h2 n (fun _=>True) hU m T=C.
  rewrite /current_support hEqual;apply:funext=>x;apply:propext;split.
  - by move=>[_ hx].
  - by move=>hx;split.
by rewrite hSupport.
Qed.
