(** Federer (1969), 4.1.11, p. 364: the original join
    of compactly supported currents. Its opaque interface exposes
    only the independently specified pushforward action. Both
    existence and uniqueness precede this seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDensityUP CurrentJoinUP CurrentJoinExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CurrentJoinSignature.
(** Source for [value]: the original join has degree i+1+j,
    Federer 4.1.11, p. 364, defining display. *)
Parameter value : forall (R : realType) (h2 : (1+1:R)!=0)
    (n i j : nat) (S : @full_current_space R h2 n i)
    (T : @full_current_space R h2 n j)
    (hS : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) i S))
    (hT : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) j T)),
  @full_current_space R h2 n (i+1+j)%N.
(** Source for [laws]: the sealed current has the original
    action on every actual compact pullback replacement,
    Federer 4.1.11, p. 364. *)
Parameter laws : forall (R : realType) (h2 : (1+1:R)!=0)
    (n i j : nat) (S : @full_current_space R h2 n i)
    (T : @full_current_space R h2 n j)
    (hS : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) i S))
    (hT : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) j T)),
  @is_current_join R h2 n i j S T (@value R h2 n i j S T hS hT).
End CurrentJoinSignature.

Module CurrentJoin : CurrentJoinSignature.
(** Source for [value]: seal the proved existence witness,
    supporting Federer 4.1.11, p. 364. *)
Definition value (R : realType) (h2 : (1+1:R)!=0)
    (n i j : nat) (S : @full_current_space R h2 n i)
    (T : @full_current_space R h2 n j)
    (hS : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) i S))
    (hT : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) j T)) :
    @full_current_space R h2 n (i+1+j)%N :=
  projT1 (cid (@current_join_exists R h2 n i j S T hS hT)).
(** Source for [laws]: the hidden witness satisfies exactly
    the independently specified original action, supporting
    Federer 4.1.11, p. 364. *)
Lemma laws (R : realType) (h2 : (1+1:R)!=0)
    (n i j : nat) (S : @full_current_space R h2 n i)
    (T : @full_current_space R h2 n j)
    (hS : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) i S))
    (hT : @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (fun _ => True)
        (fun x _ => @norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) j T)) :
  @is_current_join R h2 n i j S T (@value R h2 n i j S T hS hT).
Proof.
exact: (projT2 (cid (@current_join_exists R h2 n i j S T hS hT))).
Qed.
End CurrentJoin.
