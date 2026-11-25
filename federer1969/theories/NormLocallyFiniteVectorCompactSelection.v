(** Federer (1969), 4.1.1, p. 344: a compact
    set has a neighbourhood with only finitely many
    active terms in a locally finite vector family.
    Existing compact incidence supplies the selection. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric NormLocallyFiniteFamilyUP
  NormLocallyFiniteVectorSupports LocallyFiniteCompactNeighbourhood SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_locally_finite_vector_compact_selection]:
    all sufficiently unselected vector terms vanish on
    one common open neighbourhood of K, supporting
    smooth locally finite sums in Federer 4.1.1,
    p. 344. *)
Theorem norm_locally_finite_vector_compact_selection (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (J:choiceType) (U:set X) (I:set J) (f:J->X->Y)
    (K:smooth_compact_set hNX U):
  @open (real_norm_metric_space hNX) U ->
  is_norm_locally_finite_function_family NX U I f ->
  exists (W:set X) (F:{fset J}),@open (real_norm_metric_space hNX) W /\
    smooth_compact_carrier K `<=` W /\ W `<=` U /\
    (forall j,j \in F ->I j) /\
    forall x,W x ->forall j,I j ->j \notin F ->f j x=0.
Proof.
move=>hU hLocal.
have hSupportLocal:=@norm_locally_finite_vector_supports R X Y NX NY hNX hNY J U I f hLocal.
have [W [hW [hKW [hWU hFinite]]]]:=locally_finite_compact_open_neighbourhood hU hSupportLocal
  (smooth_compact_is_compact K) (smooth_compact_in_domain K).
pose Hit:set J:=I `&` [set j|exists x,W x /\
  closure [set y:real_norm_metric_space hNX|f j y<>0] x].
pose F:=fset_set Hit.
exists W,F; split=>//; split=>//; split=>//; split.
- move=>j; rewrite /F in_fset_set // =>/set_mem [hj hHit]; exact hj.
- move=>x hx j hj hn; case:(pselect (f j x=0))=>// hne.
  have hIn:j \in F.
    rewrite /F in_fset_set //; apply/mem_set; split=>//.
    exists x; split=>//; exact:(@subset_closure (real_norm_metric_space hNX) _ x hne).
  by move:hn; rewrite hIn.
Qed.
