(** Federer (1969), 4.1.12, p. 367: the
    finite-flat currents are the original bounded
    real functionals on the seminormed test space.
    Derive their operator laws from the actual dual
    supremum and the proved continuity criterion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet CurrentFlatNorm
  LinearSubspaceRepresentationUP LinearSubspaceRepresentationSealed CurrentEvaluation
  CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic CurrentFlatDualFiniteArithmetic
  CurrentFlatFormSeminormLaws CurrentFlatFiniteContinuity CurrentFiniteFlatSpace
  NormOperatorNormUP ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFiniteFlatOperator.
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
Local Notation C := (@current_space R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).

Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation TestFlat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation B := (@finite_flat_current_space R h2 n m U hU K).
Local Notation inc := (@finite_flat_current_inclusion R h2 n m U hU K).
Local Notation hB := (@finite_flat_current_space_laws R h2 n m U hU K).
Local Notation N := (@finite_flat_current_norm R h2 n m U hU K).

(** Source for [finite_flat_current_evaluation]: the actual
    test action of the original finite-flat subspace,
    supporting Federer 4.1.12, p. 367. *)
Definition finite_flat_current_evaluation:Hom B (Hom DT R^o):=hom_comp action inc.
Local Notation evaluation := finite_flat_current_evaluation.

(** Source for [finite_flat_current_norm_value]: the
    original F_K agrees with its real norm value on
    its finite subspace, supporting Federer 4.1.12,
    p. 367. No infinite value is truncated. *)
Lemma finite_flat_current_norm_value z:F (inc z)=(N z)%:E.
Proof.
have hFinite:=subspace_representation_member hB z.
have [a [ha hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K (action (inc z)) hFinite.
by rewrite /finite_flat_current_norm /current_flat_norm hValue.
Qed.

(** Source for [finite_flat_current_operator_norm_laws]:
    the real finite-flat value has exactly the least
    homogeneous evaluation bound, supporting the
    completeness observation in Federer 4.1.12, p. 367. *)
Lemma finite_flat_current_operator_norm_laws z:
  is_norm_operator_norm TestFlat (fun a:R^o=>`|a|) (evaluation z) (N z).
Proof.
have hValue:=finite_flat_current_norm_value z.
have hDualValue:@CurrentFlatDualSeminorm.value R h2 n m U hU K (action (inc z))=(N z)%:E:=hValue.
have hNonnegative:=@current_flat_dual_nonnegative R h2 n m U hU K (action (inc z)).
rewrite hDualValue lee_fin in hNonnegative.
constructor;first exact:hNonnegative.
- move=>phi;change (`|action (inc z) phi|<=N z * TestFlat phi).
  exact:(@current_flat_dual_finite_bound R h2 n m U hU K (action (inc z)) (N z) hDualValue phi).
- move=>a ha hBound.
  have hUpper:=@current_flat_dual_upper_from_bound R h2 n m U hU K (action (inc z)) a ha hBound.
  by rewrite hDualValue lee_fin in hUpper.
Qed.

(** Source for [finite_flat_current_operator_space_laws]:
    the actual finite-flat current space represents
    exactly all original flat-bounded real test
    functionals, supporting Federer 4.1.12, p. 367.
    The proved continuity criterion supplies fullness. *)
Theorem finite_flat_current_operator_space_laws:
  is_continuous_operator_space TestFlat (fun a:R^o=>`|a|) evaluation N.
Proof.
constructor.
- move=>z w hEqual;apply:(subspace_representation_injective hB).
  apply:current_values_extensional=>phi.
  have h:=congr1 (fun L:Hom DT R^o=>L phi) hEqual.
  by rewrite /finite_flat_current_evaluation !hom_compE in h.
- move=>z;exists (N z);split.
  + exact:norm_operator_nonnegative (finite_flat_current_operator_norm_laws z).
  + exact:norm_operator_bound (finite_flat_current_operator_norm_laws z).
- move=>L [a [ha hBound]].
  have hFinite:=@current_flat_dual_finite_from_bound R h2 n m U hU K L a ha hBound.
  have [T hValue]:=@current_finite_flat_functional_represents R h2 n m U hU K L hFinite.
  have hT:(F T < +oo)%E by rewrite /current_flat_norm hValue.
  have [z hInc]:=subspace_representation_full hB hT.
  exists z;apply:hom_ext=>phi.
  by rewrite /finite_flat_current_evaluation hom_compE hInc hValue.
- exact:finite_flat_current_operator_norm_laws.
Qed.
End CurrentFiniteFlatOperator.
