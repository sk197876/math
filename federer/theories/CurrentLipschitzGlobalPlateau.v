(** Federer (1969), 4.1.15, p. 372: perform the
    local smoothing near the original compact K using ambient
    representatives agreeing with f on an open neighbourhood.
    The cutoff and finite Lipschitz estimates are already
    proved in 4.1.14; their use here preserves the actual
    local values used in the printed radial construction. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroWhole MetricLocalLipschitzContinuity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct LipschitzUP SmoothCompactSet
  CurrentLipschitzCompactPlateau EuclideanLocalLipschitzCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_global_plateau_exists]:
    an ambient representative for the local f used in
    the smoothing proof of 4.1.15, p. 372. The
    representative agrees on an actual open neighbourhood of
    K and has one finite global Lipschitz bound.
    It is not required to map the ambient space into V. *)
Theorem current_lipschitz_global_plateau_exists (R:realType) n nu
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (f:R_n R n->R_n R nu):
  @is_locally_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f->
  exists F:R_n R n->R_n R nu,exists W:set (R_n R n),exists L:R,
    @open (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\
    (forall x,W x->F x=f x) /\ 0<L /\
    (forall x y,inner_norm (@euclidean_inner_productP R nu) (F x-F y)<=
      L*inner_norm (@euclidean_inner_productP R n) (x-y)) /\
    norm_class_zero (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R nu)) setT F.
Proof.
move=>hLocal.
have[F [W [C [hW [hKW [hWU [hAgreement [hC [hCU [hOff hFLocal]]]]]]]]]]:=
  @current_lipschitz_compact_plateau_exists R (R_n R n) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) n
    (@coordinate_basis R n) (@coordinate_basisP R n) U hU K f hLocal.
have[L [hL hBound]]:=@euclidean_local_lipschitz_compact_support_global R n
  (R_n R nu) (inner_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) F C hC hOff hFLocal.
have hContinuous:norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R nu)) setT F.
  exact:(norm_continuous_whole_class_zero
    (metric_local_lipschitz_continuous_whole hFLocal)).
exists F,W,L;split;first exact:hW.
split;first exact:hKW.
split;first exact:hWU.
split;first exact:hAgreement.
split;first exact:hL.
by split.
Qed.
