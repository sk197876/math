(** Federer (1969), 2.10.45, pp. 202–203: the translation-invariant slice
    measure is compared with Lebesgue measure on Borel sets. Applying the
    Borel regularisation of 2.2.3, p. 62, preserves invariance under a
    homeomorphism. This follows from its infimum laws and does not assume
    the original measure regular. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP TopologicalBorel ContinuousBorelPreimages
  BorelRegularisationUP BorelRegularisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regularisation_invariant_image_lower]: supporting
    infimum comparison for the Borel restriction step of
    2.10.45, pp. 202–203. A continuous surjection
    preserving the original measure's image values cannot
    decrease its regularised values. *)
Lemma borel_regularisation_invariant_image_lower (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (f : X -> X) :
  continuous f -> (forall y, exists x, f x=y) -> (forall A, mu (f @` A)=mu A) ->
    forall A, borel_regularisation mu A<=borel_regularisation mu (f @` A).
Proof.
move=> hf hsurj hinv A.
apply: (borel_regularisation_greatest (borel_regularisation_laws mu))=> B hAB hB.
have hpre : A `<=` f @^-1` B.
  move=> x hx; apply: hAB; by exists x.
have hbpre := @continuous_borel_preimage X X f hf B hB.
have hb := borel_regularisation_lower (borel_regularisation_laws mu) hpre hbpre.
have himage : f @` (f @^-1` B)=B.
  apply/seteqP; split=> y.
  - by move=> [x hx <-].
  - move=> hy; have [x hx] := hsurj y; exists x; last exact hx.
    by change (B (f x)); rewrite hx.
have he := hinv (f @^-1` B); rewrite himage in he.
by rewrite -he in hb.
Qed.

(** Source for [borel_regularisation_invariant_bijection]: supporting
    preservation of translation invariance when invoking Haar
    uniqueness in 2.10.45, p. 203. Both inverse
    maps are continuous; invariance of the second follows
    from invariance of the first, so it is not assumed. *)
Theorem borel_regularisation_invariant_bijection (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (f g : X -> X) :
  cancel f g -> cancel g f -> continuous f -> continuous g ->
  (forall A, mu (f @` A)=mu A) ->
    forall A, borel_regularisation mu (f @` A)=borel_regularisation mu A.
Proof.
move=> hgf hfg hf hg hinv A.
have hsurjf : (forall y, exists x, f x=y) by move=> x; exists (g x); exact: hfg.
have hsurjg : (forall y, exists x, g x=y) by move=> x; exists (f x); exact: hgf.
have hgfset B : g @` (f @` B)=B.
  apply/seteqP; split=> x.
  - by move=> [y [z hz <-] <-]; rewrite hgf.
  - move=> hx; exists (f x); first by exists x.
    exact: hgf.
have hfgset B : f @` (g @` B)=B.
  apply/seteqP; split=> x.
  - by move=> [y [z hz <-] <-]; rewrite hfg.
  - move=> hx; exists (g x); first by exists x.
    exact: hfg.
have hinvg B : mu (g @` B)=mu B.
  have hh := hinv (g @` B); rewrite hfgset in hh; exact: esym hh.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hb := borel_regularisation_invariant_image_lower hg hsurjg hinvg (f @` A).
  by rewrite hgfset in hb.
- exact: borel_regularisation_invariant_image_lower hf hsurjf hinv A.
Qed.
