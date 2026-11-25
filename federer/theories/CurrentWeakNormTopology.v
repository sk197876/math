(** Federer (1969), 4.1.7, pp. 357–358:
    the actual finite multivector weak dual
    has its mass-norm topology. The proof
    uses the original finite Hom expansion
    of 1.4.4, p. 20, and the
    public weak-evaluation mapping property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import TensorUP NormDifferentialUP Hom RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity NormOpenTopology
  ScalarNormExtendedEmbedding OpenFamilyTopologyUP OpenFamilyTopologyMathcomp OpenVectorTopologyUP
  DirectedSeminormVectorTopology WeakEvaluationTopologyUP GrassmannAbbreviations ExteriorGrading AlternatingForms
  NormBoundedLinearTopology ContinuousDualUP RealFunctionalNormUP
  AlternatingIsomorphism AlternatingPairing FiniteDualDimension CoefficientCoordinates CurrentCoefficientNorms
  CurrentVectorSpaces CurrentMultivectorDual MultivectorDualSealed OpenFamilyFiniteHomSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentWeakNormTopology.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation D := (exterior_power X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation hDN := (@current_vector_mass_real_norm R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation P := (norm_open_family hDN).
Local Notation W := (open_family_topological_space hO.1).
Local Notation ed := (@MultivectorDual.evaluation R X m).

(** Source for [current_weak_mass_norm_continuous]:
    the identity from the actual weak
    multivector dual to its mass-norm space
    is continuous, supporting the measurable
    density operations of Federer 4.1.7,
    pp. 357–358. Every finite degree,
    including the zero space, is retained. *)
Theorem current_weak_mass_norm_continuous:
  open_family_continuous O P (fun xi=>xi).
Proof.
have[d [b hb]]:=@current_vector_finite_basis R h2 n m.
pose I:finType:=[the finType of 'I_d].
pose a (i:I):=dual_basis hb i.
pose y (i:I):=hom_to_form (a i).
pose L (i:I):Hom D D:=hom_with_coefficient (b i) (a i).
have hEach (i:I):open_family_continuous O P (L i).
  have hCoord:open_family_continuous O (norm_open_family (@scalar_absolute_value_norm R))
      (fun xi=>ed xi (y i)).
    exact:(hO.2 D O hO.1 id).1 (@open_family_continuous_identity D O) (y i).
  have hEq:(fun xi=>ed xi (y i))=(fun xi=>a i xi).
    apply:funext=>xi;by rewrite MultivectorDual.laws /pairing /y hom_to_formK.
  rewrite hEq in hCoord.
  have hC:continuous (fun xi:W=>(a i xi:real_norm_metric_space (@scalar_absolute_value_norm R))).
    rewrite continuousP;exact:hCoord.
  have hOrbit:continuous (fun c:real_norm_metric_space (@scalar_absolute_value_norm R)=>
      (c*:b i:real_norm_metric_space hDN)).
    move=>c;exact:(@continuous_comp
      [the topologicalType of real_norm_metric_space (@scalar_absolute_value_norm R)]
      [the topologicalType of real_line_metric R]
      [the topologicalType of real_norm_metric_space hDN]
      (fun a=>(a:real_line_metric R))
      (fun a=>(a*:b i:real_norm_metric_space hDN)) c
      (@scalar_norm_real_identity_continuous R c)
      (@real_norm_metric_scalar_orbit_continuous R D DN hDN (b i) c)).
  have hActual:continuous (fun xi:W=>(L i xi:real_norm_metric_space hDN)).
    change (continuous (fun xi:W=>(a i xi*:b i:real_norm_metric_space hDN))).
    move=>xi;exact:(@continuous_comp W
      [the topologicalType of real_norm_metric_space (@scalar_absolute_value_norm R)]
      [the topologicalType of real_norm_metric_space hDN]
      (fun z=>(a i z:real_norm_metric_space (@scalar_absolute_value_norm R)))
      (fun c=>(c*:b i:real_norm_metric_space hDN)) xi (hC xi) (hOrbit (a i xi))).
  rewrite continuousP in hActual;exact:hActual.
have hVector:is_open_vector_topology P:=@seminorm_family_vector_topology R D unit (fun _=>DN) P
  (norm_single_seminorm_directed hDN) (norm_open_family_seminorm_laws hDN).
have hSum:=@open_family_finite_hom_sum_continuous R D D O P hO.1 hVector I L hEach.
have hIdentity:=@finite_Hom_coefficients R D D I b hb (hom_of_linear (linear_id D)).
change (open_family_continuous O P (hom_of_linear (linear_id D))).
rewrite hIdentity;exact:hSum.
Qed.

(** Source for [current_mass_norm_weak_continuous]:
    mass-norm continuity implies the original weak
    continuity of multivectors, supporting Federer
    4.1.7, pp. 357–358. The actual pairing
    norm bound supplies every weak coordinate. *)
Theorem current_mass_norm_weak_continuous:
  open_family_continuous P O (fun xi=>xi).
Proof.
have hP: is_open_family_topology P:=(norm_open_family_seminorm_laws hDN).1.
apply:(hO.2 D P hP id).2=>y.
pose q:Hom (Hom Y R^o) R^o:=@HomMap R (Hom Y R^o) R^o (fun f=>f y)
  (introT (asboolP _) (@hom_eval_linear R Y R^o y)).
pose L:Hom D R^o:=hom_comp q ed.
have hBound:norm_bounded_linear DN (fun r:R^o=>`|r|) L.
  exists (@current_form_comass R h2 n m y); split.
  - exact:real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n m).1 y.
  - move=>z.
    have h:=real_functional_norm_bound
      (continuous_dual_norm_laws (@current_multivector_continuous_dual R h2 n m) z) y.
    rewrite mulrC; exact:h.
have hContinuous:=@norm_bounded_linear_continuous R D R^o DN (fun r:R^o=>`|r|)
  hDN (@scalar_absolute_value_norm R) L hBound.
rewrite continuousP in hContinuous; exact:hContinuous.
Qed.
End CurrentWeakNormTopology.
