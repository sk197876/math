(** Federer (1969), 3.1.18, p. 229: linear complementary coordinates
    for the epimorphism p Df(a). Use the previously sealed coordinate
    extension of 3.1.3(3), p. 213; its implementation stays private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanEpimorphismChartUP
  EuclideanEpimorphismChartSealed EuclideanBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_epimorphism_block_chart_exists]: the linear
    complementary-coordinate isomorphism supporting g=(p f,q) in
    Federer 3.1.18, p. 229. We use a linear complement from 3.1.3(3)
    instead of requiring orthogonal complementary coordinates; the
    resulting normal-form identities and target normalization coincide. *)
Theorem euclidean_epimorphism_block_chart_exists (R:realType) v l
    (alpha:{linear R_n R (v+l)->R_n R v}) :
  (forall y, exists x, alpha x=y) ->
  exists beta gamma:Hom (R_n R (v+l)) (R_n R (v+l)),
    cancel beta gamma /\ cancel gamma beta /\
    forall x, euclidean_first_block (beta x)=alpha x.
Proof.
move=>hs.
pose w:=@EuclideanEpimorphismChart.value R (v+l) v alpha hs.
have hW:=@EuclideanEpimorphismChart.laws R (v+l) v alpha hs.
change (is_euclidean_epimorphism_chart alpha (projT1 w) (projT2 w).1 (projT2 w).2) in hW.
exists (hom_of_linear (projT2 w).1), (hom_of_linear (projT2 w).2).
split; first exact: epimorphism_chart_forward_inverse hW.
split; first exact: epimorphism_chart_backward_inverse hW.
move=>x; apply/ffunP=>i.
have hi:widen_ord (projT1 w) i=lshift l i by apply: val_inj.
have hh:=@epimorphism_chart_coordinates R (v+l) v alpha (projT1 w)
  (projT2 w).1 (projT2 w).2 hW x i.
rewrite hi in hh.
by rewrite /euclidean_first_block ffunE.
Qed.
