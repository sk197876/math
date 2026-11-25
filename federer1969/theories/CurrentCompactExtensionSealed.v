(** Federer (1969), 4.1.8, p. 361: the original
    smooth extension of a compactly supported current is
    opaque. Its public law is the independently specified
    restriction condition, with existence already proved from
    the original compact-support image in 4.1.7, p. 355. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCompactExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CompactCurrentExtensionSignature.
(** Source for [value]: the original smooth-dual extension
    of compactly supported currents, supporting Federer 4.1.8,
    p. 361, by 4.1.7, p. 355. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m),
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    [set x|@current_support R h2 n U hU m T x]->
    @current_smooth_dual_space R h2 n U hU m.
(** Source for [laws]: the opaque smooth extension
    restricts to exactly the original current, supporting
    Federer 4.1.8, p. 361. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set x|@current_support R h2 n U hU m T x]),
  @is_current_compact_extension R h2 n m U hU T (@value R h2 n m U hU T hCompact).
End CompactCurrentExtensionSignature.
Module CompactCurrentExtension:CompactCurrentExtensionSignature.
(** Source for [value]: seal a proved smooth extension
    witness; its construction serves only existence, supporting
    Federer 4.1.8, p. 361. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set x|@current_support R h2 n U hU m T x]):
    @current_smooth_dual_space R h2 n U hU m:=
  projT1 (cid (@current_compact_extension_exists R h2 n m U hU T hCompact)).
(** Source for [laws]: the sealed witness satisfies
    the independent original restriction condition, supporting
    Federer 4.1.8, p. 361. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n m:nat)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      [set x|@current_support R h2 n U hU m T x]):
  @is_current_compact_extension R h2 n m U hU T (@value R h2 n m U hU T hCompact).
Proof. exact:(projT2 (cid (@current_compact_extension_exists R h2 n m U hU T hCompact))). Qed.
End CompactCurrentExtension.
