(** Federer (1969), 4.1.8, p. 361: S(1) for
    compactly supported S uses its unique original extension
    to smooth forms. The independent restriction condition
    and its existence and uniqueness reuse 4.1.7, p. 355,
    and hence the proved compact-support image of 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactExtensionUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation CD := (@current_space R h2 n U hU m).
Local Notation ED := (@current_smooth_dual_space R h2 n U hU m).
Local Notation rho := (@current_smooth_dual_restriction R h2 n U hU m).

(** Source for [is_current_compact_extension]: the original
    smooth-dual member restricts to the given current,
    supporting S(1) in Federer 4.1.8, p. 361,
    through the compact-support image of 4.1.7, p. 355.
    This predicate assumes neither existence nor uniqueness. *)
Definition is_current_compact_extension (T:CD) (L:ED):Prop:=rho L=T.

(** Source for [current_compact_extension_exists]: every
    compactly supported current has an original smooth-dual
    extension, supporting Federer 4.1.8, p. 361,
    by the already proved image theorem of 4.1.7, p. 355. *)
Theorem current_compact_extension_exists (T:CD):
  @compact (real_norm_metric_space hNX) [set x|@current_support R h2 n U hU m T x]->
  exists L:ED,is_current_compact_extension T L.
Proof. exact:(@current_compact_support_image R h2 n m U hU T).2. Qed.

(** Source for [current_compact_extension_unique]: the
    original extension is unique by injectivity of smooth
    dual restriction, supporting S(1) in Federer 4.1.8,
    p. 361, by 4.1.7, p. 355. *)
Theorem current_compact_extension_unique (T:CD) (L M:ED):
  is_current_compact_extension T L->is_current_compact_extension T M->L=M.
Proof.
move=>hL hM.
apply:(@current_smooth_dual_restriction_injective R h2 n m U hU).
exact:(eq_trans hL (esym hM)).
Qed.
End CurrentCompactExtensionUP.
