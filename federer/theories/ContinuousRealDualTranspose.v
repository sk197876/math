(** Federer (1969), 4.1.1, p. 345: restriction and zero
    extension induce continuous linear maps on the weak duals.
    This supporting transpose theorem uses actual continuity
    and the independent evaluation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient OpenFamilyTopologyUP NormOpenTopology
  ContinuousRealDualSubspace ContinuousRealDual LinearSubspaceRepresentationUP
  LinearSubspaceLiftSealed WeakEvaluationTopologyUP WeakEvaluationTopologyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ContinuousDualTranspose.
Variable R:realType.
Variables E F:lmodType R.
Variables (O:set (set E)) (P:set (set F)).
Hypothesis hO:is_open_family_topology O.
Hypothesis hP:is_open_family_topology P.
Variable L:Hom E F.
Hypothesis hL:open_family_continuous O P L.
Local Notation DE := (@continuous_real_dual_space R E O hO).
Local Notation DF := (@continuous_real_dual_space R F P hP).
Local Notation eE := (@continuous_real_dual_evaluation R E O hO).
Local Notation eF := (@continuous_real_dual_evaluation R F P hP).
Local Notation OE := (@continuous_real_dual_weak_opens R E O hO).
Local Notation OF := (@continuous_real_dual_weak_opens R F P hP).

(** Source for [dual_transpose_precomposition]: precomposition
    with the original continuous linear map, supporting the
    two dual maps in Federer 4.1.1, p. 345. *)
Definition dual_transpose_precomposition:Hom DF (Hom E R^o):=
  hom_comp (@HomMap R (Hom F R^o) (Hom E R^o)
    (fun T=>hom_comp T L) (introT (asboolP _) (hom_precompose_linear L))) eF.

(** Source for [dual_transpose_precomposition_continuous]: the
    precomposed real functional is continuous, supporting the
    transpose maps in Federer 4.1.1, p. 345. *)
Lemma dual_transpose_precomposition_continuous T:
  continuous_real_dual_subspace hO (dual_transpose_precomposition T).
Proof.
change (open_family_continuous O
  (norm_open_family (@RealNormUP.scalar_absolute_value_norm R)) (fun x=>eF T (L x))).
exact:(open_family_continuous_compose hL
  (@continuous_real_dual_member_continuous R F P hP T)).
Qed.

(** Source for [continuous_real_dual_transpose]: the actual
    continuous-dual linear map, supporting the maps of Federer
    4.1.1, p. 345. Corestriction is opaque and already proved. *)
Definition continuous_real_dual_transpose:Hom DF DE:=
  @LinearSubspaceLift.map R DF DE (Hom E R^o)
    (continuous_real_dual_subspace hO) eE (@continuous_real_dual_model_laws R E O hO)
    dual_transpose_precomposition dual_transpose_precomposition_continuous.

(** Source for [continuous_real_dual_transpose_evaluation]:
    the transpose acts by T mapping to T composed with L,
    supporting the exact dual restriction formulas in Federer
    4.1.1, p. 345. *)
Theorem continuous_real_dual_transpose_evaluation T x:
  eE (continuous_real_dual_transpose T) x=eF T (L x).
Proof.
have h:=@LinearSubspaceLift.evaluation R DF DE (Hom E R^o)
  (continuous_real_dual_subspace hO) eE (@continuous_real_dual_model_laws R E O hO)
  dual_transpose_precomposition dual_transpose_precomposition_continuous T.
change (eE (continuous_real_dual_transpose T) x=eF T (L x)).
rewrite h /dual_transpose_precomposition !hom_compE; reflexivity.
Qed.

(** Source for [continuous_real_dual_transpose_weak_continuous]:
    the transpose is continuous for the original weak topologies,
    supporting both dual maps of Federer 4.1.1, p. 345. *)
Theorem continuous_real_dual_transpose_weak_continuous:
  open_family_continuous OF OE continuous_real_dual_transpose.
Proof.
have hEF:=@continuous_real_dual_weak_laws R E O hO.
have hFF:=@continuous_real_dual_weak_laws R F P hP.
apply:(hEF.2 DF OF hFF.1 continuous_real_dual_transpose).2=>x.
have he:(fun T:DF=>eE (continuous_real_dual_transpose T) x)=(fun T=>eF T (L x)).
  apply:funext=>T; exact:continuous_real_dual_transpose_evaluation.
rewrite he; exact:weak_evaluation_continuous hFF (L x).
Qed.
End ContinuousDualTranspose.
