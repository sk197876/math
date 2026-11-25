(** Federer (1969), 4.1.24, p. 382: the
    original integral flat infimum is subadditive. Add
    two original rectifiable decompositions with arbitrarily
    close costs, apply the preceding mass estimates,
    and pass to the infimum through its independent
    laws. No minimizing integral pair is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic
  CurrentFiniteMassLinearBound RectifiableCurrentApproximationUP RectifiableCurrentBasic
  RectifiableCurrentAlgebra IntegralCurrentClassesUP IntegralFlatSizeUP IntegralFlatSizeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section IntegralFlatSizeTriangle.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Spec:=(@is_integral_flat_size R h2 n m U hU K).
Local Notation IF:=(@is_integral_flat_current_supported_in R h2 n U hU m K).
Local Notation Size:=(@IntegralFlatSize.value R h2 n m U hU K).

(** Source for [integral_flat_size_triangle_specification]: the
    displayed original subadditivity follows from infimum
    laws alone, Federer 4.1.24, p. 382.
    The proof keeps all same-K rectifiable terms
    and exact finite mass costs. *)
Theorem integral_flat_size_triangle_specification (T S:C) a b c:
  Spec T a->Spec S b->Spec (T+S) c->c<=a+b.
Proof.
move=>hT hS hSum;case:(leP c (a+b))=>// hTooLarge.
pose delta:=(c-(a+b))/3.
have hDelta:0<delta by rewrite /delta divr_gt0 ?subr_gt0 //;lra.
have[A0 [B0 [hA0 [hB0 [hTEqual hTCost]]]]]:=
  @integral_flat_size_approximate R h2 n m U hU K T a hT delta hDelta.
have[A1 [B1 [hA1 [hB1 [hSEqual hSCost]]]]]:=
  @integral_flat_size_approximate R h2 n m U hU K S b hS delta hDelta.
have hEqual:T+S=(A0+A1)+bd (B0+B1).
  by rewrite hTEqual hSEqual (linD (hom_linear bd)) addrACA.
have hLower:=@integral_flat_size_lower R h2 n m U hU K (T+S) c hSum
  (A0+A1) (B0+B1) (rectifiable_current_add hA0 hA1)
  (rectifiable_current_add hB0 hB1) hEqual.
have[a0 [ha0 hMA0]]:=@current_finite_mass_value R h2 n m U hU A0
  (@rectifiable_current_finite_mass R h2 n m U hU K A0 hA0).
have[a1 [ha1 hMA1]]:=@current_finite_mass_value R h2 n m U hU A1
  (@rectifiable_current_finite_mass R h2 n m U hU K A1 hA1).
have[b0 [hb0 hMB0]]:=@current_finite_mass_value R h2 n m.+1 U hU B0
  (@rectifiable_current_finite_mass R h2 n m.+1 U hU K B0 hB0).
have[b1 [hb1 hMB1]]:=@current_finite_mass_value R h2 n m.+1 U hU B1
  (@rectifiable_current_finite_mass R h2 n m.+1 U hU K B1 hB1).
have hA0Upper:(M m A0<=a0%:E)%E by rewrite hMA0.
have hA1Upper:(M m A1<=a1%:E)%E by rewrite hMA1.
have hB0Upper:(M m.+1 B0<=b0%:E)%E by rewrite hMB0.
have hB1Upper:(M m.+1 B1<=b1%:E)%E by rewrite hMB1.
have hCurrentBound:=@current_finite_mass_linear_bound R h2 n m U hU
  1 A0 A1 a0 a1 hA0Upper hA1Upper.
have hFillingBound:=@current_finite_mass_linear_bound R h2 n m.+1 U hU
  1 B0 B1 b0 b1 hB0Upper hB1Upper.
rewrite scale1r normr1 mul1r in hCurrentBound.
rewrite scale1r normr1 mul1r in hFillingBound.
have hC:c<=a0+a1+(b0+b1).
  have h:=le_trans hLower (leeD hCurrentBound hFillingBound).
  by rewrite -EFinD lee_fin in h.
rewrite hMA0 hMB0 -EFinD lte_fin in hTCost.
rewrite hMA1 hMB1 -EFinD lte_fin in hSCost.
rewrite /delta in hTCost hSCost;lra.
Qed.

(** Source for [integral_flat_size_subadditive]: the actual
    original opaque size satisfies the printed triangle
    inequality, 4.1.24, p. 382. All three
    membership witnesses may be chosen independently. *)
Theorem integral_flat_size_subadditive (T S:C) (hT:IF T) (hS:IF S) (hSum:IF (T+S)):
  Size (T+S) hSum<=Size T hT+Size S hS.
Proof.
exact:(integral_flat_size_triangle_specification
  (@IntegralFlatSize.laws R h2 n m U hU K T hT)
  (@IntegralFlatSize.laws R h2 n m U hU K S hS)
  (@IntegralFlatSize.laws R h2 n m U hU K (T+S) hSum)).
Qed.
End IntegralFlatSizeTriangle.
