(** Federer (1969), 4.1.14, pp. 370–371: the original flat
    triangle and homogeneity estimates on finite flat values.
    Reuse the actual complete finite-flat norm from 4.1.12,
    p. 367, rather than introduce another seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm CurrentFiniteFlatSpace
  CurrentFiniteFlatOperator CurrentFiniteFlatCompleteness
  LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatFiniteArithmetic.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation F:=(@current_flat_norm R h2 n m U hU K).
Local Notation B:=(@finite_flat_current_space R h2 n m U hU K).
Local Notation inc:=(@finite_flat_current_inclusion R h2 n m U hU K).
Local Notation hB:=(@finite_flat_current_space_laws R h2 n m U hU K).
Local Notation hN:=(@finite_flat_current_norm_is_norm R h2 n m U hU K).

(** Source for [current_flat_finite_triangle]: the original F_E
    triangle inequality used to compare approximation sequences,
    Federer 4.1.14, pp. 370–371. Only finiteness of the two
    displayed flat values is needed, not flat-closure membership. *)
Theorem current_flat_finite_triangle (S T:C):
  (F S< +oo)%E->(F T< +oo)%E->(F ((S+T)%R)<=F S+F T)%E.
Proof.
move=>hS hT.
have[s hs]:=subspace_representation_full hB hS.
have[t ht]:=subspace_representation_full hB hT.
rewrite -hs -ht -(linD (hom_linear inc))
  !finite_flat_current_norm_value -EFinD lee_fin.
exact:real_seminorm_triangle hN.1 s t.
Qed.

(** Source for [current_flat_finite_negate]: F_E(-T)=F_E(T),
    supporting the original approximation comparisons in Federer
    4.1.14, pp. 370–371. The finite carrier is used only
    through its public inclusion and exact norm law. *)
Lemma current_flat_finite_negate (T:C):
  (F T< +oo)%E->F ((-T)%R)=F T.
Proof.
move=>hT;have[t ht]:=subspace_representation_full hB hT.
have hNeg:inc (-t)= -inc t.
  have h:=linZ (hom_linear inc) (-1:R) t.
  by rewrite !scaleN1r in h.
rewrite -ht -hNeg !finite_flat_current_norm_value.
by rewrite (real_seminorm_negate hN.1).
Qed.

(** Source for [current_flat_finite_scale]: the original
    absolute homogeneity in the extension estimate, Federer
    4.1.14, p. 371. Zero scalars and zero flat values
    retain their ordinary meanings. *)
Lemma current_flat_finite_scale c (T:C):
  (F T< +oo)%E->F ((c*:T)%R)=(`|c|%:E*F T)%E.
Proof.
move=>hT;have[t ht]:=subspace_representation_full hB hT.
rewrite -ht -(linZ (hom_linear inc)) !finite_flat_current_norm_value -EFinM.
by rewrite (real_seminorm_scale hN.1).
Qed.
End CurrentFlatFiniteArithmetic.
