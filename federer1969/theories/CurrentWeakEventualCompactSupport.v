(** Federer (1969), 4.1.14, p. 370: smooth image
    approximants lie in a prescribed compact target E eventually.
    Their original weak limit retains that same support bound.
    Reuse the earlier support criterion and constant eventual
    test-value law; no representation premise is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentSupportGeometry
  CurrentWeakSequenceLimit CurrentWeakLimitOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_weak_limit_eventual_support_compact]:
    an eventual fixed compact support bound survives the weak
    limit in the normal pushforward construction of Federer
    4.1.14, p. 370. No support condition is imposed on
    the finite initial part of the approximating sequence. *)
Theorem current_weak_limit_eventual_support_compact
    (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (u:nat->@current_space R h2 n U hU m)
    (T:@current_space R h2 n U hU m) N:
  @is_current_weak_sequence_limit R h2 n m U hU u T->
  (forall k,(N<=k)%N->@current_support R h2 n U hU m (u k)
    `<=` smooth_compact_carrier K)->
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K.
Proof.
move=>hWeak hSupport.
apply:(@current_support_compact_criterion R h2 n m U hU K T).2=>phi hPhi.
apply:(@current_weak_limit_eventual_value R h2 n m U hU u T phi 0 N hWeak)
  =>k hNk.
exact:((@current_support_compact_criterion R h2 n m U hU K (u k)).1
  (hSupport k hNk) phi hPhi).
Qed.
