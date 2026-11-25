(** Federer (1969), 4.1.8, p. 362: the original
    segment integral determines a unique actual current.
    Reuse uniqueness of the original scalar integral
    and extensionality of the genuine current space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentEvaluation
  OrientedSegmentCurrentUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [oriented_segment_current_unique]: equality
    of the original interval actions gives equality of
    the currents, supporting Federer 4.1.8, p. 362. *)
Theorem oriented_segment_current_unique (R:realType) (h2:(1+1:R)!=0) n
    (A:set (R_n R n))
    (hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x)
    (u v:R_n R n) (T S:@current_space R h2 n A hA 1%N):
  @is_oriented_segment_current R h2 n A hA u v T ->
  @is_oriented_segment_current R h2 n A hA u v S ->T=S.
Proof.
move=>hT hS;apply:(@current_values_extensional R h2 n 1%N A hA)=>phi.
exact:(EFin_inj (measure_integral_unique (hT phi) (hS phi))).
Qed.
