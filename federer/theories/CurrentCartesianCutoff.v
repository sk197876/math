(** Federer (1969), 4.1.8, p. 360: localise
    the full-space tensor-density theorem by compact scalar
    cutoffs in each original factor. The supporting laws use
    the earlier Cartesian compactness, smooth composition and
    compact-support criteria. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityBilinear NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap SmoothCompactSet CompactSupportFunctionUP
  CurrentCartesianDomain CurrentCartesianProjections CurrentCartesianCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianCutoff.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_scalar_product_class]: the
    product of the two pulled-back smooth scalar cutoffs
    is smooth on the original Cartesian domain, supporting
    Federer 4.1.8, p. 360. *)
Theorem current_cartesian_scalar_product_class (u:X->R) (v:Y->R):
  norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) u->
  norm_class_all_orders hNY (@scalar_absolute_value_norm R) (fun _=>True) v->
  norm_class_all_orders hNZ (@scalar_absolute_value_norm R) AB
    (fun z=>u (p z)*v (q z)).
Proof.
move=>hu hv k.
have hFirst:=@norm_class_compose_on R Z X R^o NZ NX (fun t:R^o=>`|t|)
  hNZ hNX (@scalar_absolute_value_norm R) AB (fun _=>True) p u k (fun _ _=>I)
  (@current_cartesian_first_projection_smooth R m n A B hA hB k) (hu k).
have hLast:=@norm_class_compose_on R Z Y R^o NZ NY (fun t:R^o=>`|t|)
  hNZ hNY (@scalar_absolute_value_norm R) AB (fun _=>True) q v k (fun _ _=>I)
  (@current_cartesian_last_projection_smooth R m n A B hA hB k) (hv k).
exact:(norm_class_scalar_product hFirst hLast).
Qed.

(** Source for [current_cartesian_compact_rectangle]: two
    original compact support bounds give their exact compact
    Cartesian bound inside A x B, supporting Federer
    4.1.8, p. 360, including empty factors. *)
Theorem current_cartesian_compact_rectangle (KA:smooth_compact_set hNX A)
    (KB:smooth_compact_set hNY B):
  exists K:smooth_compact_set hNZ AB,smooth_compact_carrier K=
    @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Proof.
pose C:=@euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
have hC:C `<=` AB.
  move=>z hz;split.
  - exact:(smooth_compact_in_domain KA (p z) hz.1).
  - exact:(smooth_compact_in_domain KB (q z) hz.2).
have hCompact:=@current_cartesian_compact R m n
  (smooth_compact_carrier KA) (smooth_compact_carrier KB)
  (smooth_compact_is_compact KA) (smooth_compact_is_compact KB).
exists (@Build_smooth_compact_set R Z NZ hNZ AB C hC hCompact);reflexivity.
Qed.

(** Source for [current_cartesian_scalar_product_support]:
    the product cutoff has support in the exact Cartesian
    product of the two original compact support bounds,
    supporting Federer 4.1.8, p. 360. *)
Theorem current_cartesian_scalar_product_support (u:X->R) (v:Y->R)
    (KA:smooth_compact_set hNX A) (KB:smooth_compact_set hNY B):
  @real_function_support R (real_norm_metric_space hNX) u `<=` smooth_compact_carrier KA->
  @real_function_support R (real_norm_metric_space hNY) v `<=` smooth_compact_carrier KB->
  @real_function_support R (real_norm_metric_space hNZ) (fun z=>u (p z)*v (q z)) `<=`
    @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Proof.
move=>hu hv.
have hCompact:=@current_cartesian_compact R m n
  (smooth_compact_carrier KA) (smooth_compact_carrier KB)
  (smooth_compact_is_compact KA) (smooth_compact_is_compact KB).
apply:(@real_function_support_in_closed_set R (real_norm_metric_space hNZ)
  (fun z=>u (p z)*v (q z))
  (@euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB))
  (compact_closed (@metric_hausdorff R (real_norm_metric_space hNZ)) hCompact))=>z hOutside.
case:(pselect (smooth_compact_carrier KA (p z)))=>hFirst.
- have hLast:~smooth_compact_carrier KB (q z) by move=>hLast;apply:hOutside;split.
  have hNot:~@real_function_support R (real_norm_metric_space hNY) v (q z).
    move=>h;exact:hLast (hv (q z) h).
  by rewrite (@real_function_zero_off_support R (real_norm_metric_space hNY) v (q z) hNot) mulr0.
- have hNot:~@real_function_support R (real_norm_metric_space hNX) u (p z).
    move=>h;exact:hFirst (hu (p z) h).
  by rewrite (@real_function_zero_off_support R (real_norm_metric_space hNX) u (p z) hNot) mul0r.
Qed.
End CurrentCartesianCutoff.
