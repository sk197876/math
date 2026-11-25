(** Federer (1969), 4.1.14, pp. 370–371: the
    original defining condition applies to the actual
    restriction of any fixed-K flat current and every
    proved compact-closure approximation. This supporting
    adapter exposes that consequence without revealing
    any construction of a candidate image. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP CurrentOpenRestriction
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationOriginal
  CurrentFlatOpenRestriction CurrentCompactPushforwardAlgebra
  CurrentFlatSequenceLimitUP CurrentSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactLipschitzImageChosenApproximation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Variable K:smooth_compact_set hNX U.
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Variable Q:@current_space R h2 nu V hV m.
Hypothesis hQ:@is_current_compact_lipschitz_image R h2 n nu m U V hU hV
  f hImage hLocal K T Q.
Variable L:R.
Variable Z:set X.
Variable g:nat->X->Y.
Hypothesis hApprox:@is_current_compact_smooth_approximation R n nu U V K f L Z g.
Local Notation hZ:=(current_compact_smooth_domain_open hApprox).
Local Notation hZU:=(@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox).
Local Notation hKZ:=(current_compact_smooth_domain_contains hApprox).
Local Notation KZ:=(@current_compact_index_in_open R n U Z K hKZ).
Local Notation S:=(@current_open_restriction R h2 n m Z U hZ hU hZU T).
Local Notation hS:=(@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat).
Local Notation hG:=(@current_compact_smooth_original_approximation R n nu U V K f L Z g hApprox).

(** Source for [current_compact_lipschitz_image_chosen_approximation]:
    apply the original convergence requirement to one actual
    restricted flat representative, Federer 4.1.14, p. 370.
    The source current need not be normal or have finite mass. *)
Theorem current_compact_lipschitz_image_chosen_approximation
    (E:smooth_compact_set hNY V)
    (hInterior:forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)):
  @is_current_flat_sequence_limit R h2 nu m V hV E
    (fun i=>@current_compact_map_pushforward R h2 n nu Z V hZ hV
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) m S
      (@flat_supported_current_compact R h2 n m Z hZ KZ S hS)) Q.
Proof.
apply:(hQ.2 E hInterior Z hZ hZU hKZ S hS _ g hG).
exact:(@flat_current_neighbourhood_inclusion_recovery R h2 n m U Z hU hZ hZU
  K hKZ T hFlat (@flat_supported_current_compact R h2 n m Z hZ KZ S hS)).
Qed.
End CurrentCompactLipschitzImageChosenApproximation.
