(** Federer (1969), 3.2.46, p. 282: the area
    localization uses maps injective on individual Borel pieces,
    without a globally injective extension. These supporting
    laws retain the actual original piece in every image cost,
    using 2.1.2, pp. 53–54, and 2.2.3, p. 61. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureImagePullback
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_piece_image_measurable]: injectivity
    only on the original piece E suffices for the image
    splitting of a source set B, supporting 3.2.46,
    p. 282. Neither f outside E nor any extension
    is required to be injective. *)
Lemma measure_piece_image_measurable (R : realType) (X Y : choiceType)
    (f : X -> Y) (nu : set Y -> \bar R) (E B : set X) :
  {in E &, injective f} -> measure_measurable nu (f @` (E `&` B)) ->
  measure_measurable (measure_restrict (measure_image_pullback f nu) E) B.
Proof.
move=> hInj hB T; rewrite /measure_restrict /measure_image_pullback (hB (f @` (E `&` T))).
have hIntersection : (f @` (E `&` T)) `&` (f @` (E `&` B))=f @` (E `&` (T `&` B)).
  apply/seteqP; split=> y.
  - move=> [[x [hEx hx] <-] [z [hEz hz] hEq]].
    have hzx : z=x := hInj _ _ (mem_set hEz) (mem_set hEx) hEq.
    exists x; last by []; split; first exact hEx; split; first exact hx.
    by rewrite -hzx.
  - move=> [x [hEx [hx hBx]] <-]; split; exists x; by split.
have hDifference : (f @` (E `&` T)) `\` (f @` (E `&` B))=f @` (E `&` (T `\` B)).
  apply/seteqP; split=> y.
  - move=> [[x [hEx hx] <-] hNot]; exists x; last by [].
    split; first exact hEx; split; first exact hx.
    move=> hBx; apply: hNot; exists x; by split.
  - move=> [x [hEx [hx hNot]] <-]; split; first by exists x; split.
    move=> [z [hEz hz] hEq].
    have hzx : z=x := hInj _ _ (mem_set hEz) (mem_set hEx) hEq.
    apply: hNot; by rewrite -hzx.
by rewrite hIntersection hDifference.
Qed.

(** Source for [measure_piece_image_borel_regular]: actual
    costs nu(f(E intersect S)) are Borel regular when
    the original piece is Borel and the restricted Borel
    images are Borel, supporting 3.2.46, p. 282.
    Use an actual equal-mass target hull and add the
    complement of E to its preimage. No arbitrary
    source-hull excess is declared null. *)
Theorem measure_piece_image_borel_regular (R : realType)
    (X Y : topologicalType) (f : X -> Y) (nu : set Y -> \bar R) (E : set X) :
  is_measure nu -> is_borel_regular_measure nu -> borel_set E ->
  {in E &, injective f} -> continuous f ->
  (forall B, borel_set B -> borel_set (f @` (E `&` B))) ->
  is_borel_regular_measure (measure_restrict (measure_image_pullback f nu) E).
Proof.
move=> hNu hRegular hE hInj hCont hImages.
pose mu := measure_restrict (measure_image_pullback f nu) E.
have hMu := measure_restrict_is_measure (measure_image_pullback_is_measure f hNu) E.
constructor.
- move=> U hU; apply: (@measure_piece_image_measurable R X Y f nu E U hInj).
  exact (@borel_regular_borel_measurable R Y nu hNu hRegular
    (f @` (E `&` U)) (@hImages U (open_borel_set hU))).
- move=> S.
  have [W [hSW [hW hMass]]] := borel_regular_cover hRegular (f @` (E `&` S)).
  pose C := (f @^-1` W) `|` ~` E.
  have hSC : S `<=` C.
    move=> x hx; case: (pselect (E x))=> hEx; last by right.
    left; apply: hSW; exists x; by split.
  exists C; split; first exact hSC; split.
  + apply: (@borel_family_binary_union X setT _ (borel_sets_family X)).
    * exact (@continuous_borel_preimage X Y f hCont W hW).
    * exact: borel_set_complement hE.
  + apply/eqP; rewrite eq_le; apply/andP; split.
    * exact (@measure_mono R X mu hMu S C hSC).
    * rewrite /measure_restrict /measure_image_pullback hMass.
      apply: (@measure_mono R Y nu hNu).
      move=> y [x [hEx [hx|hNot]] <-]; first exact hx.
      exfalso; exact: hNot hEx.
Qed.
