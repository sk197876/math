(** Federer (1969), 4.1.1, pp. 344–345: continuous real
    functionals form a vector space, even when their source is
    only a topological space. Only the target vector operations
    are used; none are assumed for the final test topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import OpenFamilyTopologyUP OpenFamilyTopologyLaws OpenVectorTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_family_constant_continuous]: constant maps
    are continuous, supporting the zero functional of both duals
    in Federer 4.1.1, pp. 344–345. *)
Lemma open_family_constant_continuous (X Y:Type)
    (O:set (set X)) (Q:set (set Y)) (c:Y) :
  is_open_family_topology O -> open_family_continuous O Q (fun _=>c).
Proof.
move=>hO A hA; case:(pselect (A c))=>[hc|hc].
- have he:[set x:X|A c]=setT.
    by apply:funext=>x; apply:propext; split.
  rewrite he; exact:open_family_whole hO.
- have he:[set x:X|A c]=set0.
    by apply:funext=>x; apply:propext; split=>// hx; exact:False_ind _ (hc hx).
  rewrite he; exact:open_family_empty hO.
Qed.

Section ContinuousOperations.
Variable R:realType.
Variable X:Type.
Variable E:lmodType R.
Variables (O:set (set X)) (Q:set (set E)).
Hypothesis hO:is_open_family_topology O.
Hypothesis hQ:is_open_vector_topology Q.
Variables f g:X->E.

(** Source for [open_family_continuous_add]: sums of continuous
    maps to a topological vector space are continuous, supporting
    the dual vector spaces in Federer 4.1.1, pp. 344–345. *)
Theorem open_family_continuous_add :
  open_family_continuous O Q f -> open_family_continuous O Q g ->
  open_family_continuous O Q (fun x=>f x+g x).
Proof.
move=>hf hg A hA; apply:(open_family_locally_open _ hO).2=>x hx.
have [B [C [hB [hC [hBx [hCx hb]]]]]]:=
  @open_vector_addition R E Q hQ (f x) (g x) A hA hx.
exists ([set y|B (f y)] `&` [set y|C (g y)]); split.
- exact:(@open_family_intersection X O hO [set y|B (f y)] [set y|C (g y)]
    (hf B hB) (hg C hC)).
- split; first by split.
  move=>y [hy hz]; exact:hb _ _ hy hz.
Qed.

(** Source for [open_family_continuous_scale]: a fixed real
    multiple of a continuous map is continuous, supporting the
    continuous duals in Federer 4.1.1, pp. 344–345. *)
Theorem open_family_continuous_scale c :
  open_family_continuous O Q f ->
  open_family_continuous O Q (fun x=>c*:f x).
Proof.
move=>hf A hA; apply:(open_family_locally_open _ hO).2=>x hx.
have [d [B [hd [hB [hBx hb]]]]]:=
  @open_vector_scaling R E Q hQ c (f x) A hA hx.
exists [set y|B (f y)]; split; first exact:hf B hB.
split=>// y hy; apply:hb hy; by rewrite subrr normr0.
Qed.
End ContinuousOperations.
