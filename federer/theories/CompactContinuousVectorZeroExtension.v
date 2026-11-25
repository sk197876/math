(** Federer (1969), 4.1.5, p. 349: a compact
    continuous vector field on the original open set is
    extended by zero before convolution. Compact support
    proves continuity at every exterior boundary point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground CompactSupportFunctionUP
  SubtypeCompactHausdorff IsotropyGroupTopology OpenSubspaceExtension CompactContinuousVectorFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactVectorExtension.
Variable R:realType.
Variable T:topologicalType.
Hypothesis hT:hausdorff_space T.
Variable U:set T.
Hypothesis hU:open U.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation X := (set_type U).

(** Source for [compact_vector_open_extension]: the original
    compact continuous input extended by zero to Euclidean
    space for Phi_e*w in Federer 4.1.5, p. 349. *)
Definition compact_vector_open_extension (w:X->Y) (x:T):Y:=
  if pselect (U x) is left h then w (exist _ x (mem_set h)) else 0.

(** Source for [compact_vector_open_extension_value]: zero
    extension preserves every original interior value used
    in Federer 4.1.5, p. 349. *)
Lemma compact_vector_open_extension_value (w:X->Y) (x:X):
  compact_vector_open_extension w (set_val x)=w x.
Proof.
rewrite /compact_vector_open_extension; case:pselect=>[h|h].
- by congr w; apply:val_inj.
- exfalso; exact:h (set_valP x).
Qed.

(** Source for [compact_vector_open_extension_outside]: zero
    values outside the original open set in the convolution
    extension of Federer 4.1.5, p. 349. *)
Lemma compact_vector_open_extension_outside (w:X->Y) (x:T):
  ~U x ->compact_vector_open_extension w x=0.
Proof. by rewrite /compact_vector_open_extension; case:pselect. Qed.

(** Source for [compact_vector_open_extension_norm]: the
    original scalar norm commutes with zero extension,
    supporting the compact convolution bounds of Federer
    4.1.5, p. 349. *)
Lemma compact_vector_open_extension_norm (w:X->Y):
  (fun x=>NY (compact_vector_open_extension w x))=
    @open_extension R T U (fun x=>NY (w x)).
Proof.
apply:funext=>x; rewrite /compact_vector_open_extension /open_extension.
case:pselect=>// _; exact:real_seminorm_zero hNY.1.
Qed.

(** Source for [compact_vector_open_extension_continuous]:
    the original zero extension of a compact continuous
    vector field is continuous on all of Euclidean space,
    as required for the smoothing argument of Federer
    4.1.5, p. 349. *)
Theorem compact_vector_open_extension_continuous (w:X->Y):
  compact_continuous_vector_fields hNY w ->
  continuous (compact_vector_open_extension w:T->real_norm_metric_space hNY).
Proof.
move=>[hw hSupport].
pose K:=@real_function_support R X (fun x=>NY (w x)).
have hK:compact (set_val @` K).
  apply:continuous_compact hSupport.
  apply:continuous_subspaceT=>x; exact:set_type_val_continuous.
have hClosed:closed (set_val @` K):=compact_closed hT hK.
have hNonzero:[set x:T|compact_vector_open_extension w x<>0] `<=` set_val @` K.
  move=>x hx.
  have hxU:U x.
    apply:contrapT=>h; apply:hx; exact:compact_vector_open_extension_outside.
  exists (exist _ x (mem_set hxU))=>//.
  apply:subset_closure=>/= hZero; apply:hx.
  rewrite -[x]/(set_val (exist _ x (mem_set hxU))) compact_vector_open_extension_value.
  exact:hNY.2 _ hZero.
move=>x; case:(pselect (U x))=>[hxU|hxU].
- pose x':X:=exist _ x (mem_set hxU).
  move=>A hA; rewrite /= nbhs_simpl /=.
  have hA':nbhs (w x':real_norm_metric_space hNY) A.
    by rewrite -(compact_vector_open_extension_value w x').
  have:=hw x' A hA'; rewrite /= nbhs_simpl /= (@nbhsE X)=>-[W [[O hO hOW] hWx] hWA].
  have hOx:O x by rewrite -hOW in hWx.
  have hNear:nbhs x (O `&` U).
    by apply:open_nbhs_nbhs; split; [exact:openI|split].
  apply:(@filterS _ _ (nbhs_filter _) _ _ _ hNear)=>y [hyO hyU] /=.
  pose y':X:=exist _ y (mem_set hyU).
  rewrite -[y]/(set_val y') compact_vector_open_extension_value.
  apply:hWA; by rewrite -hOW.
- have hNear:nbhs x (~`(set_val @` K)).
    apply:open_nbhs_nbhs; split; first exact:closed_openC hClosed.
    move=>[y _ hy]; apply:hxU; rewrite -hy; exact:set_valP.
  move=>A hA; rewrite /= nbhs_simpl /=.
  apply:(@filterS _ _ (nbhs_filter _) _ _ _ hNear)=>y hy /=.
  have hy0:compact_vector_open_extension w y=0.
    apply:contrapT=>h; apply:hy; exact:hNonzero y h.
  rewrite hy0 -(compact_vector_open_extension_outside w hxU).
  exact:nbhs_singleton hA.
Qed.

(** Source for [compact_vector_open_extension_compact]:
    the continuous zero extension retains compact support,
    for the original convolution limit of Federer 4.1.5,
    p. 349. This includes empty domains and zero fields. *)
Theorem compact_vector_open_extension_compact (w:X->Y):
  compact_continuous_vector_fields hNY w ->
  @compact_continuous_vector_fields R T Y NY hNY (compact_vector_open_extension w).
Proof.
move=>hw; split; first exact:compact_vector_open_extension_continuous hw.
rewrite compact_vector_open_extension_norm.
exact:(@open_extension_compact R T hT U hU _ (compact_continuous_vector_field_norm hw)).2.
Qed.
End CompactVectorExtension.
