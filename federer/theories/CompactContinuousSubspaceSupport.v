(** Federer (1969), 4.1.5, p. 349: compact continuous
    fields on U and their zero-normalized representatives
    in the ambient source have the same original support
    condition. The scalar correspondence also identifies
    the original K(U) majorants without changing the gauge. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground CompactSupportFunctionUP
  SubtypeCompactHausdorff IsotropyGroupTopology OpenSubspaceExtension
  CompactContinuousVectorFields CompactContinuousVectorZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactContinuousSubspaceSupport.
Variable R:realType.
Variable T:topologicalType.
Hypothesis hT:hausdorff_space T.
Variable U:set T.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.

(** Source for [compact_scalar_open_restriction]: a scalar
    compact continuous ambient representative supported in
    U restricts to the original K(U), for the majorants in
    Federer 4.1.5, p. 349. *)
Theorem compact_scalar_open_restriction (f:T->R):
  compactly_supported_continuous_functions f ->
  @real_function_support R T f `<=` U ->
  @compactly_supported_continuous_functions R (set_type U) (fun x=>f (set_val x)).
Proof.
move=>hf hSupport; split.
- move=>x; exact:continuous_comp (@set_type_val_continuous T U x) (hf.1 (set_val x)).
- apply:(@real_function_compact_support_in_closed_set R (set_type U)
    (fun x=>f (set_val x)) (set_val @^-1` (@real_function_support R T f))).
  + exact:(@set_type_compact_preimage T U _ hf.2 hSupport).
  + apply:preimage_closed (@real_function_support_closed R T f)=>x _.
    exact:set_type_val_continuous.
  + move=>x hx; exact:real_function_zero_off_support hx.
Qed.

(** Source for [compact_scalar_open_restriction_inverse]:
    zero extension of the restricted original compact
    scalar test gives the same majorant, supporting the
    literal gauge comparison in Federer 4.1.5, p. 349. *)
Lemma compact_scalar_open_restriction_inverse (f:T->R):
  @real_function_support R T f `<=` U ->
  @open_extension R T U (fun x=>f (set_val x))=f.
Proof.
move=>hSupport; apply:funext=>x.
case:(pselect (U x))=>hx.
- pose z:set_type U:=exist _ x (mem_set hx).
  exact:(@open_extensionE R T U (fun y=>f (set_val y)) z).
- rewrite (@open_extension_out R T U (fun y=>f (set_val y)) x hx).
  symmetry; apply:real_function_zero_off_support=>h; exact:hx (hSupport x h).
Qed.

(** Source for [compact_vector_open_restriction]: the actual
    compact continuous vector field supported in U gives a
    member of D on U, the extension domain in Federer
    4.1.5, p. 349. *)
Theorem compact_vector_open_restriction (w:T->Y):
  @compact_continuous_vector_fields R T Y NY hNY w ->
  @real_function_support R T (fun x=>NY (w x)) `<=` U ->
  @compact_continuous_vector_fields R (set_type U) Y NY hNY (fun x=>w (set_val x)).
Proof.
move=>hw hSupport; split.
- move=>x; exact:continuous_comp (@set_type_val_continuous T U x) (hw.1 (set_val x)).
- exact:(@compact_scalar_open_restriction (fun x=>NY (w x))
    (compact_continuous_vector_field_norm hw) hSupport).2.
Qed.

(** Source for [compact_vector_extension_support_inside]:
    the whole ambient support of the original compact
    zero extension stays inside U, needed to choose one
    small convolution scale in Federer 4.1.5, p. 349. *)
Theorem compact_vector_extension_support_inside (w:set_type U->Y):
  @compact_continuous_vector_fields R (set_type U) Y NY hNY w ->
  @real_function_support R T (fun x=>NY (@compact_vector_open_extension R T U Y w x)) `<=` U.
Proof.
move=>hw.
pose K:=@real_function_support R (set_type U) (fun x=>NY (w x)).
have hK:compact (set_val @` K).
  apply:continuous_compact hw.2.
  apply:continuous_subspaceT=>x; exact:set_type_val_continuous.
have hClosed:closed (set_val @` K):=compact_closed hT hK.
have hSupport:@real_function_support R T
    (fun x=>NY (@compact_vector_open_extension R T U Y w x)) `<=` set_val @` K.
  apply:(@real_function_support_in_closed_set R T
    (fun x=>NY (@compact_vector_open_extension R T U Y w x)) (set_val @` K) hClosed)=>x hx.
  case:(pselect (U x))=>hU.
  - pose z:set_type U:=exist _ x (mem_set hU).
    rewrite -[x]/(set_val z) (@compact_vector_open_extension_value R T U Y w z).
    apply:(@real_function_zero_off_support R (set_type U) (fun x=>NY (w x)) z)=>hz.
    apply:hx; by exists z.
  - by rewrite (@compact_vector_open_extension_outside R T U Y w x hU)
      (real_seminorm_zero hNY.1).
move=>x hx; have[z _ hz]:=hSupport x hx.
rewrite -hz; exact:set_valP.
Qed.
End CompactContinuousSubspaceSupport.
