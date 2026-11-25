(** Federer (1969), 4.1.22, p. 379: existence of
    the independently specified abelian-group carriers. The
    existing subgroup predicate supplies the subtype group;
    this construction serves only as an existence witness. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import TopologicalGroupUP AdditiveSubgroupRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section AdditiveSubgroupModel.
Variable V:zmodType.
Variable S:set V.
Hypothesis hS:is_subgroup (fun x y:V=>x+y) (fun x=>-x) 0 S.

(** Source: a boolean membership predicate for the existence
    model only, supporting Federer 4.1.22, p. 379. *)
Definition additive_subgroup_model_pred (v:V):=`[< S v >].
(** Source: a subtype existence model of the original subgroup,
    supporting Federer 4.1.22, p. 379. *)
Record additive_subgroup_model:=AdditiveSubgroupElement{
  additive_subgroup_model_value:V;
  additive_subgroup_model_proof:
    additive_subgroup_model_pred additive_subgroup_model_value
}.
(** Source: the eliminator for that existence model,
    supporting Federer 4.1.22, p. 379. *)
Definition additive_subgroup_model_rect (P:additive_subgroup_model->Type)
    (h:forall v hv,P (@AdditiveSubgroupElement v hv))
    (z:additive_subgroup_model):P z:=
  match z as z' return P z' with @AdditiveSubgroupElement v hv=>h v hv end.
HB.instance Definition _ := [isSub for additive_subgroup_model_value
  by additive_subgroup_model_rect].
HB.instance Definition _ := [Choice of additive_subgroup_model by <:].

(** Source: original additive-subgroup closure gives the
    subtype abelian-group witness, supporting 4.1.22, p. 379. *)
Lemma additive_subgroup_model_closed:
  GRing.zmod_closed additive_subgroup_model_pred.
Proof.
split;first by apply/asboolP;exact:subgroup_unit hS.
move=>x y /asboolP hx /asboolP hy;apply/asboolP.
exact:(@TopologicalGroupUP.subgroup_mul V (fun a b:V=>a+b)
  (fun a=>-a) 0 S hS x (-y) hx
  (@TopologicalGroupUP.subgroup_inv V (fun a b:V=>a+b) (fun a=>-a) 0 S hS y hy)).
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubZmodule.Build V
  additive_subgroup_model_pred additive_subgroup_model additive_subgroup_model_closed.

(** Source: the existence-model inclusion is additive,
    supporting the abelian groups of 4.1.22, p. 379. *)
Lemma additive_subgroup_model_value_additive:zmod_morphism additive_subgroup_model_value.
Proof.
move=>x y;change (val (x-y)=val x-val y);exact:raddfB.
Qed.
HB.instance Definition _ := GRing.isZmodMorphism.Build additive_subgroup_model V
  additive_subgroup_model_value additive_subgroup_model_value_additive.

(** Source: the additive inclusion of the witness carrier,
    supporting Federer 4.1.22, p. 379. *)
Definition additive_subgroup_model_inclusion:
    {additive additive_subgroup_model->V}:=
  GRing.Additive.clone _ _ additive_subgroup_model_value _.

(** Source for [additive_subgroup_representation_exists]: every
    prescribed additive subgroup admits the original injective
    additive carrier with exactly that image, supporting Federer
    4.1.22, p. 379. The empty generating family still has
    the zero group, so no nonempty-set assumption is introduced. *)
Theorem additive_subgroup_representation_exists:
  exists W:zmodType,exists inc:{additive W->V},
    is_additive_subgroup_representation S inc.
Proof.
exists [the zmodType of additive_subgroup_model],additive_subgroup_model_inclusion.
constructor.
- exact:val_inj.
- move=>w;apply/asboolP;exact:additive_subgroup_model_proof.
- move=>v hv.
  exists (@AdditiveSubgroupElement v (introT (asboolP _) hv));by [].
Qed.
End AdditiveSubgroupModel.
