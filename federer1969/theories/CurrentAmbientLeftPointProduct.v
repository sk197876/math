(** Federer (1969), 4.1.11, p. 366: the lower
    and upper prism faces are the original point-product
    inclusions of their simplex. Reuse the preceding
    point-product theorem and the proved affine image law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentDirac CurrentCartesianDomain CurrentCartesianPointInclusion
  CurrentCompactPointProduct CurrentCompactPushforwardAlgebra CurrentCartesianMapPullback
  CurrentJoinAffineSourcePushforward CurrentDomainTransport CurrentDomainTransportPushforward
  CurrentAmbientCartesianProduct CurrentPointInclusionAffine OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexCurrentAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientLeftPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)%N).
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n) (hFull m) (hFull n)).
Variable a:X.
Local Notation inclusion := (@current_cartesian_point_inclusion R m n a).
Local Notation hAffine := (@current_point_inclusion_affine R m n a).
Local Notation Image := (fun y hy=>@current_cartesian_point_inclusion_image R m n
  (Full m) (Full n) a Logic.I y hy).
Local Notation FullImage := (fun (y:Y) (_:True)=>Logic.I).
Local Notation Smooth := (@current_cartesian_point_inclusion_smooth R m n (Full n) (hFull n) a).
Local Notation AGlobal := (@euclidean_affine_map_smooth R n (m+n)%N
  (Full n) (hFull n) inclusion hAffine).
Local Notation AClass := (@current_cartesian_factor_open_class R n (m+n)%N
  (Full n) (hFull n) inclusion AGlobal).

(** Source for [current_ambient_left_point_product]:
    delta_a times T is the original affine inclusion
    image under u mapped to (a,u), supporting Federer
    4.1.11, p. 366. T is an arbitrary compact
    current; no representation hypothesis is added. *)
Theorem current_ambient_left_point_product j
    (T:@current_space R h2 n (Full n) (hFull n) j)
    (hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n (Full n) (hFull n) j T)):
  @current_ambient_cartesian_product R h2 m n 0%N j
    (@dirac_current R h2 m (Full m) (hFull m) a) T=
  @current_join_affine_current R h2 n (m+n)%N inclusion hAffine j T hT.
Proof.
have hOriginal:=@current_compact_point_product R h2 m n j
  (Full m) (Full n) (hFull m) (hFull n) a Logic.I T hT.
have hDomain:=@current_domain_transport_compact_pushforward R h2 n (m+n)%N
  (Full n) AB (Full (m+n)%N) (hFull n) hAB (@current_cartesian_full_domain R m n)
  (hFull (m+n)%N) inclusion Image FullImage Smooth j T hT.
rewrite /current_ambient_cartesian_product hOriginal hDomain /current_join_affine_current.
have hClass:Smooth=AClass:=Prop_irrelevance _ _.
by rewrite hClass.
Qed.

(** Source for [current_ambient_left_point_simplex]: the
    original point product with [u_0,...,u_j] is
    [(a,u_0),...,(a,u_j)], supporting both prism faces
    in Federer 4.1.11, p. 366. Repeated vertices,
    degree zero and zero-dimensional factors are included. *)
Theorem current_ambient_left_point_simplex j (v:'I_(j.+1)->Y):
  @current_ambient_cartesian_product R h2 m n 0%N j
    (@dirac_current R h2 m (Full m) (hFull m) a)
    (@OrientedSimplexCurrent.value R h2 n j v)=
  @OrientedSimplexCurrent.value R h2 (m+n)%N j
    (fun k=>@euclidean_block_join R m n (a,v k)).
Proof.
pose hV:=@oriented_simplex_current_compact R h2 n j v.
rewrite (@current_ambient_left_point_product j (@OrientedSimplexCurrent.value R h2 n j v) hV).
exact:(@oriented_simplex_current_affine R h2 n (m+n)%N inclusion hAffine j v hV).
Qed.
End CurrentAmbientLeftPointProduct.
