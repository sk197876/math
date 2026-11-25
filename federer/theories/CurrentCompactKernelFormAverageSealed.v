(** Federer (1969), 4.1.18, p. 374: seal the
    proved smooth kernel average behind its independent
    literal coefficient-integral specification. The slice
    and cutoff witnesses remain hidden.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain SmoothCompactSet
  CurrentKernelAverageUP CurrentCompactKernelFormAverageUP
  CurrentCompactKernelFormAverageExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentCompactKernelFormAverageSignature.
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n q j:nat)
  (U:set (R_n R q))
  (hU:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R q)) U x)
  (w:R_n R n->R)
  (S:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) 0%N)
  (hS:@is_current_kernel_average R h2 n w S)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun _=>True)) (hOff:forall z,~smooth_compact_carrier K z->w z=0),
  Hom (@current_smooth_space R h2 (n+q)
    (@euclidean_cartesian_set R n q (fun _=>True) U)
    (@current_cartesian_domain_open R n q (fun _=>True) U
      (fun x _=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) hU) (0+j))
    (@current_smooth_space R h2 q U hU j).
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n q j:nat)
  (U:set (R_n R q))
  (hU:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R q)) U x)
  (w:R_n R n->R)
  (S:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) 0%N)
  (hS:@is_current_kernel_average R h2 n w S)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun _=>True)) (hOff:forall z,~smooth_compact_carrier K z->w z=0),
  @is_current_compact_kernel_form_average R h2 n q j U hU w
    (@value R h2 n q j U hU w S hS K hOff).
End CurrentCompactKernelFormAverageSignature.
Module CurrentCompactKernelFormAverage:CurrentCompactKernelFormAverageSignature.
Definition value (R:realType) (h2:(1+1:R)!=0) (n q j:nat)
  (U:set (R_n R q))
  (hU:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R q)) U x)
  (w:R_n R n->R)
  (S:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) 0%N)
  (hS:@is_current_kernel_average R h2 n w S)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun _=>True)) (hOff:forall z,~smooth_compact_carrier K z->w z=0):=
  projT1 (cid (@current_compact_kernel_form_average_exists R h2 n q j U hU
    w S hS K hOff)).
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n q j:nat)
  (U:set (R_n R q))
  (hU:forall x,U x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R q)) U x)
  (w:R_n R n->R)
  (S:@current_space R h2 n (fun _=>True)
    (fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) 0%N)
  (hS:@is_current_kernel_average R h2 n w S)
  (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun _=>True)) (hOff:forall z,~smooth_compact_carrier K z->w z=0):
  @is_current_compact_kernel_form_average R h2 n q j U hU w
    (@value R h2 n q j U hU w S hS K hOff).
Proof.
exact:projT2 (cid (@current_compact_kernel_form_average_exists R h2 n q j U hU
  w S hS K hOff)).
Qed.
End CurrentCompactKernelFormAverage.
Arguments CurrentCompactKernelFormAverage.value : clear implicits.
Arguments CurrentCompactKernelFormAverage.laws : clear implicits.
