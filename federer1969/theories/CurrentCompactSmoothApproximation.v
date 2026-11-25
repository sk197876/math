(** Federer (1969), 4.1.14, p. 370: public existence of the
    compact smooth approximation from the original locally Lipschitzian
    map. Consumers use the independent specification or the opaque
    selected pair; Kirszbraun and convolution witnesses stay hidden. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP SmoothCompactSet
  LipschitzUP LipschitzConstant OpenLocalLipschitzCompact
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximationExistence
  CurrentCompactSmoothApproximationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactSmoothApproximation.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable K:smooth_compact_set hNX U.
Variable f:X->Y.
Hypothesis hLocal:@is_locally_metric_lipschitz R XT YT U f.
Hypothesis hMap:forall x,U x->V (f x).

(** Source for [current_lipschitz_compact_smooth_approximation_exists]:
    the existence of the original smooth approximants in Federer
    4.1.14, p. 370. The bound is the least attained Lip(f restricted
    to K), by 2.2.7, p. 64, and the extension in 2.10.43, p. 201.
    No global Lipschitz bound on f or convexity of V is required. *)
Theorem current_lipschitz_compact_smooth_approximation_exists:
  exists L:R,exists Z:set X,exists g:nat->X->Y,
    @is_least_metric_lipschitz_constant R XT YT (smooth_compact_carrier K) f L /\
    @is_current_compact_smooth_approximation R n nu U V K f L Z g.
Proof.
have hKLocal:=@norm_open_local_lipschitz_compact R X Y NX NY hNX hNY U f
  (smooth_compact_carrier K) hU hLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
pose L:=metric_lipschitz_constant hKLocal.
have hLeast:@is_least_metric_lipschitz_constant R XT YT
    (smooth_compact_carrier K) f L:=metric_lipschitz_constant_specification hKLocal.
have hImageK:forall x,smooth_compact_carrier K x->V (f x).
  move=>x hx;exact:hMap x (smooth_compact_in_domain K x hx).
have[Z [g hg]]:=@current_compact_smooth_approximation_exists R n nu
  U V hU hV K f L (least_metric_lipschitz_bound hLeast) hImageK.
exists L,Z,g;split;[exact:hLeast|exact:hg].
Qed.
End CurrentCompactSmoothApproximation.
