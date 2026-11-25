(** Federer (1969), 4.1.23, p. 379:
    restore the literal original open U after
    the full-space construction. Actual restriction
    preserves the full-hull real polyhedral class,
    does not increase mass, and gives the
    original same-C flat-error bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentMassSealed CurrentFlatNorm
  CurrentOpenRestriction CurrentOpenRestrictionMass CurrentFlatOpenRestriction
  CurrentLipschitzCompactImage SmoothCompactSet SmoothCompactSetExtensionality
  NormalCurrentsUP PolyhedralCurrentAlgebra PolyhedralOpenRestriction
  PolyhedralApproximationUP NormalCurrentAmbientInclusion NormalFullPolyhedralApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OriginalNormalApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation Current := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation MF := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Restrict := (@current_open_restriction R h2 n m U Full hU hFull
  (fun _ _ => Logic.I)).
Variables K C : smooth_compact_set hNX U.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NX (smooth_compact_carrier C) x.
Variable T : Current.
Hypothesis hNormal : @normal_currents_supported_in R h2 n U hU m K T.

(** Source for [normal_polyhedral_flat_mass_approximation]:
    the completed normal-input assertion
    on every original open U,
    Federer 4.1.23, p. 379.
    The original K and C,
    both quantitative bounds and full
    generator hulls are retained. *)
Theorem normal_polyhedral_flat_mass_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current,
    @is_polyhedral_flat_mass_approximation R h2 n m U hU C T epsilon P.
Proof.
pose includeU := fun (x : X) (_ : U x) => Logic.I.
pose KF := @current_compact_index_in_open R n U Full K (fun _ _=>Logic.I).
pose CF := @current_compact_index_in_open R n U Full C (fun _ _=>Logic.I).
have [Q [hNormalQ [hRecovery hMassQ]]] :=
  @normal_current_ambient_inclusion R h2 n m U hU K T hNormal.
have [P [hPoly [hError hMass]]] := @normal_full_polyhedral_approximation R h2 n m
  KF CF hKC Q hNormalQ epsilon hEpsilon.
have hBack : @current_compact_index_in_open R n Full U CF
    (smooth_compact_in_domain C)=C.
  by apply: smooth_compact_set_extensionality.
have hPolyU := @real_polyhedral_current_open_restriction R h2 n m Full U hFull hU
  includeU CF (smooth_compact_in_domain C) P hPoly.
rewrite hBack in hPolyU.
have hNorm := @current_open_restriction_flat_norm_le R h2 n m Full U hFull hU
  includeU CF (smooth_compact_in_domain C) (Q-P).
rewrite hBack (linB (hom_linear Restrict)) hRecovery in hNorm.
have hMassU := @current_open_restriction_mass_bound R h2 n m U Full hU hFull includeU P.
exists (Restrict P); split; first exact: hPolyU.
split; first exact: le_trans hNorm hError.
exact: le_trans (le_trans hMassU hMass) (leeD hMassQ (lexx epsilon%:E)).
Qed.
End OriginalNormalApproximation.
