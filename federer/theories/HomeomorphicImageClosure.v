(** Federer (1969), 3.2.36, pp. 272--273:
    supporting closure transport through the
    actual Euclidean block homeomorphism. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_image_closure_subset]:
    general topology supporting the original-
    source closure reduction in Federer 3.2.36,
    pp. 272--273. A continuous map sends
    the source closure into the image closure.
    Closed inverse images and the least-closed-
    superset property prove this; it is not
    an additional theorem attributed to Federer. *)
Lemma continuous_image_closure_subset (X Y:topologicalType) (f:X->Y) (A:set X):
  continuous f ->f @` closure A `<=` closure (f @` A).
Proof.
move=>hf y [x hx <-].
pose C:=f @^-1` closure (f @` A).
have hC:closed C.
  apply:preimage_closed; last exact:closed_closure.
  by move=>z _; exact:hf.
have hCover:A `<=` C.
  move=>z hz; apply:subset_closure; by exists z.
have hClosure:=@closureS X A C hCover x hx.
exact:hC x hClosure.
Qed.

(** Source for [homeomorphic_image_closure]: supporting
    exact closure transport in the Cartesian
    product formula of Federer 3.2.36,
    pp. 272--273. Two continuous inverse
    maps preserve closure on every subset.
    Their independent inverse and continuity
    laws suffice; no global homeomorphism
    object is selected and no source
    measurability is assumed. *)
Lemma homeomorphic_image_closure (X Y:topologicalType) (f:X->Y) (g:Y->X) (A:set X):
  cancel f g ->cancel g f ->continuous f ->continuous g ->
  closure (f @` A)=f @` closure A.
Proof.
move=>hGF hFG hf hg.
have hImage:g @` (f @` A)=A.
  apply/seteqP; split.
  - by move=>x [y [z hz <-] <-]; rewrite hGF.
  - move=>x hx; exists (f x); last exact:hGF x; by exists x.
apply/seteqP; split.
- move=>y hy.
  have hG:closure (g @` (f @` A)) (g y).
    apply:(continuous_image_closure_subset hg); by exists y.
  rewrite hImage in hG.
  exists (g y); first exact:hG.
  exact:hFG y.
- exact:continuous_image_closure_subset hf.
Qed.
