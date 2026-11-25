(** Federer (1969), 4.1.24, p. 382:
    two finite-mass decompositions of the
    same current have a normal difference
    of fillings in the original common
    compact K. Compact support is kept
    explicit; finite masses alone give
    local normality. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentBoundary
  CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentFiniteMassRepresentation NormalCurrentsUP
  SmoothCompactSet CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FillingDifference.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation NC := (@current_space R h2 n U hU m.+1).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation NextM := (@CurrentMass.value R h2 n m.+1 U hU).
Local Notation bd := (@current_boundary R h2 n m U hU).

(** Source for [current_finite_filling_difference_boundary]:
    equal decompositions give
    boundary(S_1-S_2)=R_2-R_1,
    the last argument of Federer 4.1.24,
    p. 382. This is an actual
    current identity in every output degree. *)
Lemma current_finite_filling_difference_boundary
    (A1 A2:C) (S1 S2:NC):
  A1+bd S1=A2+bd S2->bd (S1-S2)=A2-A1.
Proof.
move=>hEqual.
have hFirst:bd S1= -A1+(A2+bd S2).
  by rewrite -hEqual addrA addNr add0r.
rewrite (linB (hom_linear bd)) hFirst -addrA addrK.
exact:addrC.
Qed.

(** Source for [current_finite_filling_difference_locally_normal]:
    the four finite masses in Federer
    4.1.24, p. 382, give finite
    mass and boundary mass of S_1-S_2.
    No compactness is needed for this
    local-normality conclusion. *)
Theorem current_finite_filling_difference_locally_normal
    (A1 A2:C) (S1 S2:NC):
  (M A1< +oo)%E->(M A2< +oo)%E->
  (NextM S1< +oo)%E->(NextM S2< +oo)%E->
  A1+bd S1=A2+bd S2->
  @is_locally_normal_current R h2 n U hU m.+1 (S1-S2).
Proof.
move=>hA1 hA2 hS1 hS2 hEqual.
have hMass:(NextM (S1-S2)< +oo)%E.
  have h:=@current_finite_mass_linear_combination
    R h2 n m.+1 U hU (-1) S2 S1 hS2 hS1.
  by rewrite scaleN1r addrC in h.
have hBoundary:(M (bd ((S1-S2)%R))< +oo)%E.
  rewrite (current_finite_filling_difference_boundary hEqual).
  have h:=@current_finite_mass_linear_combination
    R h2 n m U hU (-1) A1 A2 hA1 hA2.
  by rewrite scaleN1r addrC in h.
split.
- exact:current_finite_mass_representation hMass.
- exact:current_finite_mass_representation hBoundary.
Qed.

(** Source for [current_finite_filling_difference_normal]:
    in the common compact K of the
    two decompositions, the filling difference
    is normal, as used for the exact
    flat minimiser in Federer 4.1.24,
    p. 382. The original K is
    retained, without a larger support set. *)
Theorem current_finite_filling_difference_normal
    (K:smooth_compact_set hNX U)
    (A1 A2:C) (S1 S2:NC):
  (M A1< +oo)%E->(M A2< +oo)%E->
  (NextM S1< +oo)%E->(NextM S2< +oo)%E->
  A1+bd S1=A2+bd S2->
  (forall x,@current_support R h2 n U hU m.+1 S1 x->
    smooth_compact_carrier K x)->
  (forall x,@current_support R h2 n U hU m.+1 S2 x->
    smooth_compact_carrier K x)->
  @normal_currents_supported_in R h2 n U hU m.+1 K (S1-S2).
Proof.
move=>hA1 hA2 hS1 hS2 hEqual hSupport1 hSupport2.
have hSupport:forall x,
    @current_support R h2 n U hU m.+1 (S1-S2) x->
      smooth_compact_carrier K x.
  have h:=@current_support_linear_subset
    R h2 n m.+1 U hU K (-1) S2 S1 hSupport2 hSupport1.
  by rewrite scaleN1r addrC in h.
split;last exact:hSupport.
split.
- exact:current_finite_filling_difference_locally_normal
    hA1 hA2 hS1 hS2 hEqual.
- exact:(@current_support_compact_bound R h2 n m.+1 U hU K (S1-S2) hSupport).
Qed.
End FillingDifference.
