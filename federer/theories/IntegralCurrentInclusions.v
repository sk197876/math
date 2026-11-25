(** Federer (1969), 4.1.24, p. 381: the original
    inclusion diagram, with integer upper classes, real
    lower classes, and every original compact index retained.
    Derive the inclusions from literal definitions, the
    earlier polyhedral boundary theorem and the existing
    normal and flat laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentBoundarySquared
  CurrentSupportGeometry CurrentMassSealed CurrentFiniteMassRepresentation
  CompactRepresentedCurrentMass NormalCurrentsUP FlatCurrentsUP FlatCurrentClosure
  FlatCurrentBoundary CurrentNormalOriginalFlat PolyhedralCurrentAlgebra
  PolyhedralCurrentBoundary RectifiableCurrentApproximationUP RectifiableCurrentBasic
  RectifiableCurrentWitnesses IntegralCurrentClassesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralCurrentInclusions.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(fun m=>@current_space R h2 n U hU m).
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation Rect:=(fun m=>@is_rectifiable_current_supported_in R h2 n m U hU K).
Local Notation Integral:=(fun m=>@is_integral_current_supported_in R h2 n U hU m K).
Local Notation IntegralFlat:=(fun m=>@is_integral_flat_current_supported_in R h2 n U hU m K).

(** Source for [integral_current_is_rectifiable_supported]: the
    original arrow I_(m,K) into R_(m,K), with the
    separate zero-degree definition, Federer 4.1.24, p. 381. *)
Theorem integral_current_is_rectifiable_supported m (T:C m):Integral m T->Rect m T.
Proof. by case:m T=>[|j] T hT;[exact:hT|exact:hT.1]. Qed.

(** Source for [integral_polyhedral_current_integral_supported]:
    the first arrow of the original upper row,
    Federer 4.1.24, p. 381. Positive boundaries are
    the existing integer simplex face sums with exactly K. *)
Theorem integral_polyhedral_current_integral_supported m (T:C m):
  @integral_polyhedral_current_class R h2 n m U hU K T->Integral m T.
Proof.
case:m T=>[|j] T hT.
- exact:integral_polyhedral_current_rectifiable_supported hT.
- split;first exact:integral_polyhedral_current_rectifiable_supported hT.
  apply:integral_polyhedral_current_rectifiable_supported.
  exact:integral_polyhedral_current_boundary_supported hT.
Qed.

(** Source for [rectifiable_current_is_integral_flat_supported]:
    the original arrow R_(m,K) into script-F_(m,K),
    Federer 4.1.24, p. 381. The zero rectifiable
    filling is allowed for every degree and empty K. *)
Theorem rectifiable_current_is_integral_flat_supported m (T:C m):
  Rect m T->IntegralFlat m T.
Proof.
move=>hT;exists T,(0:C m.+1);split;first exact:hT.
split;first exact:rectifiable_current_zero.
by rewrite (lin0 (hom_linear (@current_boundary R h2 n m U hU))) addr0.
Qed.

(** Source for [integral_current_normal_supported]: the original
    vertical arrow I_(m,K) into N_(m,K), Federer
    4.1.24, p. 381. Finite masses and both required
    integration representations are derived from rectifiability;
    support remains exactly within the original compact K. *)
Theorem integral_current_normal_supported m (T:C m):
  Integral m T->@normal_currents_supported_in R h2 n U hU m K T.
Proof.
move=>hT.
have hRect:=integral_current_is_rectifiable_supported hT.
have hSupport:=@rectifiable_current_support R h2 n m U hU K T hRect.
have hMass:=@rectifiable_current_finite_mass R h2 n m U hU K T hRect.
split;last exact:hSupport.
split;last exact:(@current_support_compact_bound R h2 n m U hU K T hSupport).
split;first exact:(@current_finite_mass_representation R h2 n m U hU T hMass).
case:m T hT hRect hSupport hMass=>[|j] T hT hRect hSupport hMass;first exact:I.
exact:(@current_finite_mass_representation R h2 n j U hU
  (@current_boundary R h2 n j U hU T)
  (@rectifiable_current_finite_mass R h2 n j U hU K _ hT.2)).
Qed.

(** Source for [integral_flat_current_is_flat_supported]: the
    last vertical arrow of the diagram, Federer 4.1.24,
    p. 381. Actual rectifiable decompositions give original
    flat membership in the same K, even when M(T)
    itself is infinite. *)
Theorem integral_flat_current_is_flat_supported m (T:C m):
  IntegralFlat m T->@is_flat_current_supported_in R h2 n m U hU K T.
Proof.
move=>[A [S [hA [hS ->]]]].
pose Flat:=@flat_current_subspace R h2 n m U hU K.
apply:(@subspace_add R (C m) Flat).
- exact:(@rectifiable_current_flat_supported R h2 n m U hU K A hA).
- apply:(@flat_current_boundary_supported R h2 n m U hU K S).
  exact:(@rectifiable_current_flat_supported R h2 n m.+1 U hU K S hS).
Qed.

(** Source for [integral_current_boundary_supported]: boundary
    preserves the original integral classes with the same K,
    a consequence of 4.1.24's definition on p. 381
    and the preceding boundary-squared identity. Zero output
    degree has its original separate integral definition. *)
Theorem integral_current_boundary_supported m (T:C m.+1):
  Integral m.+1 T->Integral m (@current_boundary R h2 n m U hU T).
Proof.
case:m T=>[|j] T hT;first exact:hT.2.
split;first exact:hT.2.
rewrite current_boundary_squared;exact:rectifiable_current_zero.
Qed.
End IntegralCurrentInclusions.

(** Source for [normal_current_flat_finite_mass]: the
    central arrow of the lower row in 4.1.24,
    p. 381, follows from the original normal-to-flat
    inclusion and finite mass of compactly supported
    integration-representable currents. *)
Theorem normal_current_flat_finite_mass (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  @is_normal_current R h2 n U hU m T->
  @is_flat_current R h2 n m U hU T /\
    (@CurrentMass.value R h2 n m U hU T< +oo)%E.
Proof.
move=>hT;split;first exact:(@current_normal_original_flat R h2 n m U hU T hT).
exact:(@compact_represented_current_finite_mass R h2 n m U hU T hT.1.1 hT.2).
Qed.
