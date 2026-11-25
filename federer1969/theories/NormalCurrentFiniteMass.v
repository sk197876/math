(** Federer (1969), 4.1.7, p. 358: every
    normal current has finite normal mass.
    Its current and positive-degree boundary are
    represented and compactly supported; the
    original variation measures are therefore finite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet FunctionalSupportUP CurrentSpaces CurrentBoundary
  CurrentBoundarySupport CurrentSupportGeometry CurrentIntegrationCriterion CompactRepresentedCurrentMass
  CurrentMassSealed NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section NormalCurrentFiniteMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation M := (fun m=>@CurrentMass.value R h2 n m U hU).
Local Notation bd := (fun m=>@current_boundary R h2 n m U hU).

(** Source for [normal_current_finite_normal_mass]:
    if T is normal then N(T)<infinity,
    Federer 4.1.7, p. 358, sentence
    preceding the normal-current vector spaces.
    Degree zero uses only the current mass. *)
Theorem normal_current_finite_normal_mass m (T:C m):
  @is_normal_current R h2 n U hU m T->
    (@current_normal_mass R h2 n U hU m T < +oo)%E.
Proof.
case:m T=>[|d] T [hLocal hCompact].
- exact:(@compact_represented_current_finite_mass R h2 n 0 U hU T hLocal.1 hCompact).
- have hCurrent:=@compact_represented_current_finite_mass R h2 n d.+1 U hU T hLocal.1 hCompact.
  pose K:smooth_compact_set hNX U:=@Build_smooth_compact_set R (R_n R n) NX hNX U
    (@current_support R h2 n U hU d.+1 T) (fun x hx=>hx.1) hCompact.
  have hBoundaryCompact:=@current_support_compact_bound R h2 n d U hU K (bd d T)
    (@current_boundary_support_subset R h2 n d U hU T).
  have hBoundary:=@compact_represented_current_finite_mass R h2 n d U hU (bd d T)
    hLocal.2 hBoundaryCompact.
  exact:lte_add_pinfty hCurrent hBoundary.
Qed.
End NormalCurrentFiniteMass.
