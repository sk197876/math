(** Federer (1969), 4.1.5, p. 349: compact
    continuous fields on U may be represented by their
    ambient zero extensions. Continuity and the original
    norm support specify their vector space independently
    of the later distribution extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP VectorDaniellHypotheses
  CompactContinuousVectorFields CompactContinuousVectorSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousDomainFields.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.

(** Source for [compact_continuous_domain_fields]: the actual
    compact continuous extension domain D in Federer
    4.1.5, p. 349, represented by ambient fields whose
    whole compact support is contained in U. *)
Definition compact_continuous_domain_fields:set (X->Y):=
  [set w|@compact_continuous_vector_fields R X Y NY hNY w /\
    @real_function_support R X (fun x=>NY (w x)) `<=` U].

(** Source for [compact_continuous_domain_fields_off]: the
    representative vanishes outside the original open
    source, as used for Phi_e*w in Federer 4.1.5,
    p. 349. *)
Lemma compact_continuous_domain_fields_off w:
  compact_continuous_domain_fields w ->forall x,~U x ->w x=0.
Proof.
move=>hw x hx.
apply:(@compact_continuous_vector_zero_off_norm_support R X Y NY hNY w x)=>h.
exact:hx (hw.2 x h).
Qed.

(** Source for [compact_continuous_domain_vector_space]:
    closure of the original compact continuous D under
    sums and scalar multiples in Federer 4.1.5,
    p. 349. No compactness of the whole U is assumed. *)
Theorem compact_continuous_domain_vector_space:
  is_vector_function_space compact_continuous_domain_fields.
Proof.
have hQ:=@compact_continuous_vector_space R X Y NY hNY.
constructor.
- split; first exact:vector_function_space_zero hQ.
  have hZero:(fun _:X=>NY (0:Y))=(fun _:X=>(0:R)).
    apply:funext=>x; exact:real_seminorm_zero hNY.1.
  rewrite hZero /real_function_support.
  have hEmpty:[set x:X|(0:R)<>0]=set0 by apply:funext=>x; apply:propext; split.
  by rewrite hEmpty closure0.
- move=>w v hw hv; split; first exact:(@vector_function_space_add R X Y (@compact_continuous_vector_fields R X Y NY hNY) hQ w v hw.1 hv.1).
  have hUnion:@real_function_support R X (fun x=>NY (w x+v x)) `<=`
      (@real_function_support R X (fun x=>NY (w x)) `|`
       @real_function_support R X (fun x=>NY (v x))).
    apply:(@real_function_support_in_closed_set R X (fun x=>NY (w x+v x)) _
      (closedU (@real_function_support_closed R X _) (@real_function_support_closed R X _)))=>x hx.
    have hw0:w x=0.
      apply:(@compact_continuous_vector_zero_off_norm_support R X Y NY hNY w x)=>h; apply:hx; by left.
    have hv0:v x=0.
      apply:(@compact_continuous_vector_zero_off_norm_support R X Y NY hNY v x)=>h; apply:hx; by right.
    by rewrite hw0 hv0 addr0 (real_seminorm_zero hNY.1).
  move=>x hx; have[h|h]:=hUnion x hx; [exact:hw.2 x h|exact:hv.2 x h].
- move=>c w hw; split; first exact:(@vector_function_space_scale R X Y (@compact_continuous_vector_fields R X Y NY hNY) hQ c w hw.1).
  have hSupport:@real_function_support R X (fun x=>NY (c*:w x)) `<=`
      @real_function_support R X (fun x=>NY (w x)).
    apply:(@real_function_support_in_closed_set R X (fun x=>NY (c*:w x)) _
      (@real_function_support_closed R X (fun x=>NY (w x))))=>x hx.
    by rewrite (@compact_continuous_vector_zero_off_norm_support R X Y NY hNY w x hx)
      scaler0 (real_seminorm_zero hNY.1).
  move=>x hx; exact:hw.2 x (hSupport x hx).
Qed.
End CompactContinuousDomainFields.
