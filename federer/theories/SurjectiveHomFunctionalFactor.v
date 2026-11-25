(** Federer (1969), 4.1.19, p. 377: the
    converse descends the bounded pair functional
    through the original surjective q after
    proving annihilation of its actual kernel.
    This supporting algebraic step exposes only
    existence and uniqueness of the linear factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [surjective_hom_functional_factor_exists]:
    factor the pair functional through q in
    the converse of Federer 4.1.19,
    p. 377. The original onto map
    and its actual kernel are retained. No
    arbitrary complement or chosen factor is public. *)
Theorem surjective_hom_functional_factor_exists (K : fieldType)
    (P W Z : lmodType K) (q : Hom P W) (beta : Hom P Z) :
  (forall w, exists v, q v=w) -> (forall v, q v=0 -> beta v=0) ->
  exists F : Hom W Z, forall v, F (q v)=beta v.
Proof.
move=> hOnto hKernel.
have hFibre (v w : P) : q v=q w -> beta v=beta w.
  move=> hEqual.
  have hZero : q (v-w)%R=0.
    by rewrite (linB (hom_linear q)) hEqual subrr.
  have hBeta := hKernel (v-w)%R hZero.
  rewrite (linB (hom_linear beta)) in hBeta.
  by apply/eqP; rewrite -subr_eq0; apply/eqP.
have [r hR] := choice hOnto.
pose f := fun w : W => beta (r w).
have hAgree (v : P) : f (q v)=beta v.
  apply: hFibre; exact: hR.
have hLinear : linear f.
  move=> a x y.
  have hImage : q (a*:r x+r y)%R=a*:x+y.
    by rewrite (hom_linear q) (hR x) (hR y).
  rewrite -hImage hAgree (hom_linear beta).
  by [].
exists (@HomMap K W Z f (introT (asboolP _) hLinear)).
exact: hAgree.
Qed.

(** Source for [surjective_hom_functional_factor_unique]:
    onto q gives uniqueness in the converse
    of Federer 4.1.19, p. 377.
    Equality is on all actual currents in
    the original flat union. *)
Theorem surjective_hom_functional_factor_unique (K : fieldType)
    (P W Z : lmodType K) (q : Hom P W) (beta : Hom P Z)
    (F G : Hom W Z) :
  (forall w, exists v, q v=w) -> (forall v, F (q v)=beta v) ->
  (forall v, G (q v)=beta v) -> F=G.
Proof.
move=> hOnto hF hG; apply: hom_ext=> w.
have [v <-] := hOnto w.
exact: (eq_trans (hF v) (esym (hG v))).
Qed.
