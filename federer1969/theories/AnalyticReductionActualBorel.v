(** Federer (1969), 3.4.8(5), p. 328:
    all original A_j, B_j, C_m and E_m sets
    are Borel for the actual coordinate and
    orthogonal germ data. Definitions and implementations
    remain behind the proved opaque interfaces.
    No ideal closedness, compact witnesses or Borel
    assertion is added to the original hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing
  CommutativeIdealUP AnalyticCoordinateGermsSealed AnalyticCoordinateSubringFamilyUP
  AnalyticCoordinateSubringFamilySealed AnalyticReductionLociUP AnalyticReductionActual
  AnalyticRotatedGermIdeal AnalyticPrefixGermSubring AnalyticReductionABorel
  AnalyticReductionBBorel AnalyticReductionCBorel AnalyticReductionEBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Borel.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation Q:=(@AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega).
Local Notation rotated:=(@analytic_rotated_germ_ideal R X B hB n e he I).
Local Notation A:=(@analytic_reduction_actual_A R X B hB n e he omega I).
Local Notation Bj:=(@analytic_reduction_actual_B R X B hB n e he omega I).
Local Notation C:=(@analytic_reduction_actual_C R X B hB n e he omega I).
Local Notation E:=(@analytic_reduction_actual_E R X B hB n e he omega I).

(** Source for [analytic_reduction_actual_A_borel]: every
    original A_j, including A_0, is Borel,
    3.4.8(5), p. 328. *)
Lemma analytic_reduction_actual_A_borel j:borel_set (A j).
Proof.
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
have hSame:A j = [set g:O|(0<j)%N /\exists alpha,rotated g alpha /\Q j alpha /\alpha<>0].
  apply/seteqP;split=>g.
  - exact:(analytic_reduction_A_membership hLaws j g).1.
  - exact:(analytic_reduction_A_membership hLaws j g).2.
rewrite hSame (analytic_coordinate_subring_family_member hQLaws (ltn_ord j)).
exact:(@analytic_reduction_A_borel R X B hB n e he omega hDual I j (ltn_ord j) hI).
Qed.

(** Source for [analytic_reduction_actual_B_borel]: every
    original B_(j+1) is Borel, with its actual
    positive derivative test, 3.4.8(5), p. 328. *)
Lemma analytic_reduction_actual_B_borel j:borel_set (Bj j).
Proof.
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
have hSame:Bj j = [set g:O|exists alpha,rotated g alpha /\Q (j:nat).+1 alpha /\
    has_nonzero_analytic_directional_jet alpha (e j)].
  apply/seteqP;split=>g.
  - exact:(analytic_reduction_B_membership hLaws j g).1.
  - exact:(analytic_reduction_B_membership hLaws j g).2.
rewrite hSame (analytic_coordinate_subring_family_member hQLaws (ltn_ord j)).
exact:(@analytic_reduction_B_borel R X B hB n e he omega hDual I j hI).
Qed.

(** Source for [analytic_reduction_actual_C_borel]: every
    original C_m is Borel with the actual
    gamma_j, Q_j and I_g, 3.4.8(5), p. 328. *)
Lemma analytic_reduction_actual_C_borel m:borel_set (C m).
Proof.
have hLaws:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hQLaws:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
have hSame:C m = [set g:O|forall j:'I_n,(m<=j)%N ->exists delta L,
    Q m delta /\~rotated g delta /\Q (m:nat).+1 L /\rotated g (delta*gamma j-L)].
  apply/seteqP;split=>g.
  - exact:(analytic_reduction_C_membership hLaws m g).1.
  - exact:(analytic_reduction_C_membership hLaws m g).2.
rewrite hSame (analytic_coordinate_subring_family_member hQLaws (ltnW (ltn_ord m)))
  (analytic_coordinate_subring_family_member hQLaws (ltn_ord m)).
exact:(@analytic_reduction_C_borel R X B hB n e he omega hDual I gamma m hI).
Qed.

(** Source for [analytic_reduction_actual_E_borel]: every
    original E_m, including E_n and the n=0
    case, is Borel, 3.4.8(5), p. 328. *)
Lemma analytic_reduction_actual_E_borel j:borel_set (E j).
Proof.
exact:(@analytic_reduction_E_borel_from_membership R X NX hNX n O e gamma Q rotated A Bj C E
  (@analytic_reduction_actual_laws R X B hB n e he omega I)
  analytic_reduction_actual_A_borel analytic_reduction_actual_B_borel analytic_reduction_actual_C_borel j).
Qed.
End Borel.
