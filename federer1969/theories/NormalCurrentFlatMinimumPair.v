(** Federer (1969), 4.1.24, p. 382: each
    original normal series increment has an exact
    normal mass-minimizing pair in the same K.
    This is the attained normal-filling clause of
    4.1.12, pp. 367–368, with its residual. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentSupportGeometry CurrentBoundary CurrentBoundarySupport
  CurrentMassSealed CompactRepresentedCurrentMass NormalCurrentsUP
  NormalCurrentLinear NormalCurrentBoundary CurrentFlatNorm CurrentFlatMinimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormalCurrentFlatMinimumPair.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation Normal:=(fun d=>@normal_currents_supported_in R h2 n U hU d K).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).

(** Source for [normal_current_flat_minimum_pair]: exact
    same-K normal decomposition of each original normal
    increment in 4.1.24's series proof, p. 382.
    No larger compact or price error is introduced. *)
Theorem normal_current_flat_minimum_pair (T:C):
  Normal m T->exists A:C,exists B:Next,
    Normal m A /\Normal m.+1 B /\T=A+bd B /\(M m A+M m.+1 B=F T)%E.
Proof.
move=>hT.
have hFinite:=@compact_represented_current_finite_mass R h2 n m U hU T hT.1.1.1 hT.1.2.
have[B [hB hMinimum]]:=@current_flat_minimum_normal_filling
  R h2 n m U hU K T hT.2 hFinite.
pose A:=T-bd B.
have hBoundaryNormal:=@normal_current_boundary R h2 n U hU m B hB.
have hBoundarySupport:@current_support R h2 n U hU m (bd B) `<=` smooth_compact_carrier K.
  move=>x hx;apply:hMinimum.1.
  exact:(@current_boundary_support_subset R h2 n m U hU B x hx).
have hANormal:@is_normal_current R h2 n U hU m A.
  have h:=@normal_current_linear R h2 n U hU m (-1) (bd B) T hBoundaryNormal hT.1.
  by rewrite scaleN1r addrC in h.
have hASupport:@current_support R h2 n U hU m A `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1)
    (bd B) T hBoundarySupport hT.2.
  by rewrite scaleN1r addrC in h.
exists A,B;split;first exact:conj hANormal hASupport.
split;first exact:conj hB hMinimum.1.
split;first by rewrite /A subrK.
exact:esym hMinimum.2.1.
Qed.
End NormalCurrentFlatMinimumPair.
