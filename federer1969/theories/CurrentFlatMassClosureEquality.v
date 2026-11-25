(** Federer (1969), 4.1.12, p. 368: if the
    compact support index carries no nonzero normal
    filling, its original flat closure equals its
    mass closure. Retain the literal two approximation
    predicates and use the already proved equality
    of mass and flat norm on original flat chains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet NormalCurrentsUP
  FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure FlatCurrentMassNoFillings CurrentNormalMassClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_mass_closures_equal_no_fillings]:
    F_(m,K) is exactly the M closure of N_(m,K)
    if K supports no nonzero normal (m+1)-current.
    This proves the original closure assertion in
    Federer 4.1.12, p. 368, without assuming
    finite mass or support of the candidate T. *)
Theorem current_flat_mass_closures_equal_no_fillings (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hNoFilling:forall S:@current_space R h2 n U hU m.+1,
      @is_normal_current R h2 n U hU m.+1 S->
      @current_support R h2 n U hU m.+1 S `<=` smooth_compact_carrier K->S=0)
    (T:@current_space R h2 n U hU m):
  @is_flat_current_supported_in R h2 n m U hU K T<->
  @is_normal_current_mass_closure R h2 n m U hU K T.
Proof.
split;last exact:(@normal_current_mass_closure_is_flat R h2 n m U hU K T).
move=>hFlat epsilon hEpsilon.
have[S [hNormal hApprox]]:=hFlat epsilon hEpsilon.
have hSFlat:=@supported_normal_current_is_flat R h2 n m U hU K S hNormal.
have hDifference:@is_flat_current_supported_in R h2 n m U hU K (T-S).
  exact:(@subspace_sub R _ (@flat_current_subspace R h2 n m U hU K) T S hFlat hSFlat).
have[hEqual hFinite]:=@flat_current_mass_equals_flat_no_fillings R h2 n m U hU K hNoFilling (T-S) hDifference.
exists S;split;first exact:hNormal.
by rewrite -hEqual.
Qed.
