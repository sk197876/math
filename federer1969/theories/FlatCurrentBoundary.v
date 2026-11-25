(** Federer (1969), 4.1.12, p. 368: the
    boundary of a positive-dimensional flat chain
    in F_(m,K)(U) lies in F_(m-1,K)(U).
    Use the exact preceding flat bound and the
    original normal-current boundary theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentBoundary
  CurrentBoundarySupport NormalCurrentBoundary FlatCurrentsUP CurrentFlatBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation NC := (@current_space R h2 n U hU m.+1).
Local Notation boundary := (@current_boundary R h2 n m U hU).

(** Source for [flat_current_boundary_supported]: the
    original boundary preserves flat closure with the
    same compact K, Federer 4.1.12, p. 368.
    The positive input degree is explicit. *)
Theorem flat_current_boundary_supported (T:NC):
  @is_flat_current_supported_in R h2 n m.+1 U hU K T->
    @is_flat_current_supported_in R h2 n m U hU K (boundary T).
Proof.
move=>hFlat epsilon hEpsilon.
have [S [[hNormal hSupport] hApprox]]:=@hFlat epsilon hEpsilon.
exists (boundary S);split.
- split.
  + exact:(@normal_current_boundary R h2 n U hU m S hNormal).
  + move=>x hx;exact:hSupport x (@current_boundary_support_subset R h2 n m U hU S x hx).
- have hBound:=@current_flat_boundary_bound R h2 n m U hU K (T-S).
  rewrite (linB (hom_linear boundary)) in hBound.
  exact:le_lt_trans hBound hApprox.
Qed.
End FlatCurrentBoundary.
