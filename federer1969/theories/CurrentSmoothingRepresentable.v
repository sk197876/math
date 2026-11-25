(** Federer (1969), 4.1.18, p. 375: every
    original smoothed current has a genuine Radon
    integration representation, even when the input
    current is not representable or has infinite mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentIntegrationCriterion SmoothingKernelUP SmoothingDilationUP
  CurrentSmoothingOperators CurrentSmoothingSmoothDensity
  CurrentSmoothLebesgueFullRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_smoothing_representable]: the
    smooth density from 4.1.2, p. 347,
    gives the actual original variation of T_epsilon
    used in Federer 4.1.18, p. 375. *)
Theorem current_smoothing_representable (R:realType) (h2:(1+1:R)!=0)
    n m (phi:R_n R n->R) (family:R->R_n R n->R)
    (hPhi:is_smoothing_kernel phi) (hFamily:is_smoothing_dilation phi family)
    (T:@current_space R h2 n (fun _=>True)
      (fun x _=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) m)
    epsilon (hEpsilon:0<epsilon):
  @is_integration_representable_current R h2 n m (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x)
    (@current_smoothing R h2 n m phi family hPhi hFamily T epsilon).
Proof.
have [xi hEqual]:=@current_smoothing_smooth_lebesgue_exists R h2 n m
  phi family hPhi hFamily epsilon hEpsilon T.
rewrite hEqual;exact:current_smooth_lebesgue_representable.
Qed.
Arguments current_smoothing_representable : clear implicits.
