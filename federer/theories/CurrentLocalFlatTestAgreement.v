(** Federer (1969), 4.1.14, p. 371: agreement
    on each compact family of target tests with
    an original flat current gives local flatness.
    This is the preceding exact point criterion
    from 4.1.12, p. 368, applied on compact
    neighbourhoods inside the original open target. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates SmoothCompactSet SmoothCompactNeighbourhoods
  CurrentSpaces CurrentSupportGeometry CurrentSupportAgreement FlatCurrentsUP LocallyFlatPointCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_local_flat_test_agreement]: the
    current defined by original local compact flat
    actions is locally flat, supporting Federer
    4.1.14, p. 371. The smaller agreement
    neighbourhood is derived, not assumed. *)
Theorem current_local_flat_test_agreement
    (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  (forall K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U,
    exists S:@current_space R h2 n U hU m,
      @is_flat_current R h2 n m U hU S /\
      forall phi:@current_test_space R h2 n U hU m,
        @current_test_support R h2 n m U hU phi `<=` smooth_compact_carrier K ->
        @current_value R h2 n U hU m T phi=@current_value R h2 n U hU m S phi) ->
  @is_locally_flat_current R h2 n m U hU T.
Proof.
move=>hLocal;apply:(@locally_flat_point_criterion R h2 n m U hU T).2=>x hx.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose J:=@smooth_compact_singleton R X NX hNX U x hx.
have[K hK]:=@smooth_compact_neighbourhood_exists R X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU J.
have[S [hFlat hAgreement]]:=hLocal K.
pose O:=@interior (real_norm_metric_space hNX) (smooth_compact_carrier K).
have hO:@open (real_norm_metric_space hNX) O:=open_interior _.
have hPoint:O x.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX
    (smooth_compact_carrier K) x).1 (hK x (erefl x)).
have hAgree:forall phi:@current_test_space R h2 n U hU m,
    @current_test_support R h2 n m U hU phi `<=` O ->
    @current_value R h2 n U hU m T phi=@current_value R h2 n U hU m S phi.
  move=>phi hPhi;apply:hAgreement=>y hy;exact:interior_subset (hPhi y hy).
have hOutside:=@current_support_difference_agreement R h2 n m U hU T S O hO hAgree.
exists S;split;first exact:hFlat.
move=>hSupport;exact:(hOutside x hSupport).2 hPoint.
Qed.
