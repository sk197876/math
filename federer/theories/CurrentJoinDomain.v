(** Federer (1969), 4.1.11, p. 364: the original ordered
    domain R^n times R times R^n and its actual [0,1] factor.
    These are aliases of the preceding Euclidean product and opaque
    segment, with their existing openness and containing-domain laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentSegmentMapUP OrientedSegmentCurrentSealed CurrentJoinMapSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinDomain.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (n+(1+n))%N).
Local Notation Full := (fun _ : X => True).
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation NZ :=
  (inner_norm (@euclidean_inner_productP R (n+(1+n))%N)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (t : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace :=
  (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).

(** Source for [current_join_domain]: the original x,t,y domain,
    Federer 4.1.11, p. 364. The ordered Euclidean product is the
    already specified and proved block product of 2.6.5. *)
Definition current_join_domain : set Z :=
  @euclidean_cartesian_set R n (1+n)%N Full TimeSpace.

(** Source for [current_join_domain_open]: the original product
    is open, supporting the join definition in Federer 4.1.11,
    p. 364. Reuse the existing openness law for each block product. *)
Definition current_join_domain_open :
  forall z, current_join_domain z ->
    norm_domain_interior NZ current_join_domain z :=
  @current_cartesian_domain_open R n (1+n)%N
    Full TimeSpace hFull hTimeSpace.

(** Source for [current_join_map_image]: F has values in the
    original full Euclidean target, Federer 4.1.11, p. 364. *)
Definition current_join_map_image :
  forall z, current_join_domain z -> Full (@CurrentJoinMap.value R n z)
  := fun _ _ => Logic.I.

(** Source for [current_join_time_segment_domain]: the whole
    original [0,1] lies in its time factor, supporting the join
    definition in Federer 4.1.11, p. 364. *)
Definition current_join_time_segment_domain :
  @is_current_segment_domain R 1%N Time
    (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) :=
  fun _ _ => Logic.I.

(** Source for [current_join_time_segment]: the original [0,1]
    in S times [0,1] times T, Federer 4.1.11, p. 364. This
    reuses the actual opaque segment of 4.1.8, p. 362. *)
Definition current_join_time_segment (h2 : (1+1:R)!=0) :
    @current_space R h2 1%N Time hTime 1%N :=
  @OrientedSegmentCurrent.value R h2 1%N Time hTime
    (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
    current_join_time_segment_domain.
End CurrentJoinDomain.
