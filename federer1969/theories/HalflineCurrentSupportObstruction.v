(** Federer (1969), 4.1.7, p. 359:
    the actual support obstruction in the
    original half-line example. Any whole-line
    current supported in (0,b] has compact
    support, so its boundary cannot be the
    unit point mass at b. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanOneNormDifferential MetricClosedBalls FiniteNormBoundedCompact
  CurrentSpaces CurrentBoundary CurrentDirac CurrentSupportGeometry CurrentCompactBoundaryObstruction SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineCurrentSupportObstruction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation C := (@current_space R h2 1 (fun _=>True) hFull 1%N).

(** Source for [halfline_current_supported_primitive_impossible]:
    no S in D_1(R) with boundary delta_b
    has support contained in (0,b], exactly
    the obstruction asserted in Federer 4.1.7,
    p. 359. This conclusion is independent
    of the printed primitive-uniqueness qualification. *)
Theorem halfline_current_supported_primitive_impossible b (hb:0<b) (S:C):
  (forall x,@current_support R h2 1 (fun _=>True) hFull 1%N S x->0<x ord0<=b) ->
  @current_boundary R h2 1 0%N (fun _=>True) hFull S<>
    @dirac_current R h2 1 (fun _=>True) hFull (euclidean_one_embed b).
Proof.
move=>hSupport.
pose B:=@metric_closed_ball R (real_norm_metric_space hNX) 0 b.
have hB:compact B.
  exact:(@finite_norm_metric_boundedly_compact R X NX hNX 1
    (@coordinate_basis R 1) (@coordinate_basisP R 1) 0 b (ltW hb)).
pose K:=@Build_smooth_compact_set R X NX hNX (fun _=>True) B (fun _ _=>Logic.I) hB.
have hCompact:compact [set x:real_norm_metric_space hNX|
    @current_support R h2 1 (fun _=>True) hFull 1%N S x].
  apply:(@current_support_compact_bound R h2 1 1%N (fun _=>True) hFull K S)=>x hx.
  have /andP [hx0 hxb]:=hSupport x hx.
  change (is_true (NX (0-x)<=b)).
  by rewrite sub0r (real_seminorm_negate hNX.1) euclidean_one_norm_coordinate
    (ger0_norm (ltW hx0)).
exact:(@current_compact_boundary_not_dirac R h2 1 (fun _=>True) hFull S
  (euclidean_one_embed b) Logic.I hCompact).
Qed.
End HalflineCurrentSupportObstruction.
