(** Federer (1969), 4.1.1, pp. 343–344: private existence of
    E(U,Y). The normalized subtype is only an existence witness;
    the public space is specified by its independent evaluation laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations SmoothFunctionSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothFunctionConstruction.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Local Notation F := (GRing.Lmodule.clone R (X->Y) _).

(** Source for [smooth_function_pred]: private subtype membership
    for the existence proof of E(U,Y), Federer 4.1.1, p. 343.
    The zero-outside convention identifies actual functions on U. *)
Definition smooth_function_pred (f:F) :=
  `[< norm_class_all_orders hNX hNY U f /\ forall x,~U x -> f x=0 >].

(** Source for [SmoothFunctionWitness]: actual-function witness
    for the abstract space E(U,Y), Federer 4.1.1, p. 343. *)
Record SmoothFunctionWitness (hOpen:forall x,U x -> norm_domain_interior NX U x) := SmoothFunctionMap {
  (** Source for [smooth_function_value_witness]: evaluation of
      the private function-space witness, Federer 4.1.1, p. 343. *)
  smooth_function_value_witness : X->Y;
  (** Source for [smooth_function_member_witness]: the private
      evaluation is smooth on U, Federer 4.1.1, p. 343. *)
  smooth_function_member_witness : smooth_function_pred smooth_function_value_witness
}.

(** Source for [smooth_function_rect_witness]: subtype elimination
    supporting the existence of E(U,Y), Federer 4.1.1, p. 343. *)
Definition smooth_function_rect_witness (P:SmoothFunctionWitness hU->Type)
    (h:forall f hf,P (@SmoothFunctionMap hU f hf)) (z:SmoothFunctionWitness hU) : P z :=
  match z as z' return P z' with @SmoothFunctionMap _ f hf=>h f hf end.
HB.instance Definition _ := [isSub for (@smooth_function_value_witness hU) by smooth_function_rect_witness].
HB.instance Definition _ := [Choice of (SmoothFunctionWitness hU) by <: ].

(** Source for [smooth_function_closed_witness]: the smooth
    functions form a vector space under pointwise operations,
    Federer 4.1.1, p. 343, using the class laws in 3.1.11. *)
Lemma smooth_function_closed_witness : GRing.submod_closed smooth_function_pred.
Proof.
split.
- apply/asboolP; split; last by move=>x hx.
  move=>k; exact:(@norm_class_constant R X Y NX NY hNX hNY U 0 k hU).
- move=>c f g /asboolP [hf hf0] /asboolP [hg hg0]; apply/asboolP; split.
  + move=>k; exact:(norm_class_add (norm_class_scale c (hf k)) (hg k)).
  + move=>x hx; change (c*:f x+g x=0).
    by rewrite (hf0 x hx) (hg0 x hx) scaler0 addr0.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build R F
  smooth_function_pred (SmoothFunctionWitness hU) smooth_function_closed_witness.

(** Source for [smooth_function_space_witness]: proved existence
    of the independent E(U,Y) laws, Federer 4.1.1, pp. 343–344.
    Empty U and zero-dimensional source and target spaces remain. *)
Theorem smooth_function_space_witness :
  is_smooth_function_space hNX hNY U (@smooth_function_value_witness hU).
Proof.
constructor.
- by move=>c f g x.
- move=>f; exact:(elimT (asboolP _) (@smooth_function_member_witness hU f)).1.
- move=>f; exact:(elimT (asboolP _) (@smooth_function_member_witness hU f)).2.
- exact:val_inj.
- move=>f hf.
  pose g x:=if asbool (U x) then f x else 0.
  have hg x:U x -> g x=f x.
    move=>hx; rewrite /g; case:asboolP=>[h|h] //; exact:False_ind _ (h hx).
  have hg0 x:~U x -> g x=0.
    move=>hx; rewrite /g; case:asboolP=>[h|h] //; exact:False_ind _ (hx h).
  have hclass:norm_class_all_orders hNX hNY U g.
    move=>k; apply:(@norm_class_domain_agreement R X Y NX NY hNX hNY U f g k _ (hf k)).
    by move=>x hx; symmetry; exact:hg.
  have hgpred:smooth_function_pred g by apply/asboolP; split.
  exists (@SmoothFunctionMap hU g hgpred); exact:hg.
Qed.
End SmoothFunctionConstruction.
