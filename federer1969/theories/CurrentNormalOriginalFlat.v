(** Federer (1969), 4.1.12, p. 368, used in
    4.1.14, p. 372: every original normal
    current belongs to the compact flat union.
    Its own compact support is a valid index
    because the current itself is a normal approximant.
    No such assertion is made for arbitrary flat currents. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet NormalCurrentsUP FlatCurrentsUP FlatCurrentFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_normal_original_flat]: the original
    inclusion N_m(U) into F_m(U), Federer 4.1.12,
    p. 368. The compact index is hidden in
    the proof; the conclusion is the original union. *)
Theorem current_normal_original_flat (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m)
    (hNormal:@is_normal_current R h2 n U hU m T) :
  @is_flat_current R h2 n m U hU T.
Proof.
pose K:=@Build_smooth_compact_set R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U
  (@current_support R h2 n U hU m T) (fun x hx=>hx.1) hNormal.2.
exists K;apply:(@supported_normal_current_is_flat R h2 n m U hU K T).
split;first exact:hNormal.
by move=>x hx.
Qed.
