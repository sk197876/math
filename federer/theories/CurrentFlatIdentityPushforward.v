(** Federer (1969), 4.1.15, p. 373: support coincidence
    compares a retraction with identity. The actual
    flat-union identity image is the original current, by
    4.1.14 smooth agreement and the old 4.1.10 identity law.
    The compact index is chosen only inside this proof. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CurrentOpenIdentitySmooth CurrentElementaryPushforwards
  CurrentCompactPushforwardAlgebra CurrentLipschitzCompactImage
  CurrentCompactLipschitzPushforwardSmooth CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_flat_lipschitz_identity_pushforward]:
    identity fixes T in F_m(U), by the original formal
    properties in Federer 4.1.14, p. 371, used in
    4.1.15, p. 373. The current need not be normal
    or have finite mass, and U may be empty. *)
Theorem current_flat_lipschitz_identity_pushforward
    (R : realType) (h2 : (1+1:R)!=0) n m
    (U : set (R_n R n))
    (hU : forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hImage : forall x,U x->U x)
    (hLocal : @is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      U (fun x=>x))
    (T : @current_space R h2 n U hU m)
    (hFlat : @is_flat_current R h2 n m U hU T) :
  @CurrentFlatLipschitzPushforward.value R h2 n n m U U hU hU
    (fun x=>x) hImage hLocal T hFlat=T.
Proof.
have [K hK] := hFlat.
rewrite (@CurrentFlatLipschitzPushforward.compact_value R h2 n n m U U hU hU
  (fun x=>x) hImage hLocal T hFlat K hK).
pose hSmooth := @current_open_identity_smooth R n U hU.
rewrite (@current_compact_lipschitz_pushforward_smooth R h2 n n m U U hU hU
  (fun x=>x) hImage hLocal K T hK hSmooth).
exact: (@current_compact_identity_pushforward R h2 n U hU m T
  (@flat_supported_current_compact R h2 n m U hU K T hK) hImage hSmooth _).
Qed.
