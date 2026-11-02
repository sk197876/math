(** General topology supporting Federer (1969), 3.2.28,
    pp. 263–267: isometric ambient coordinates preserve
    the relative openness required by 3.1.19(3), p. 231. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import HomeomorphismUP EuclideanSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [homeomorphism_relative_open_images]: invariance
    of relative openness under ambient coordinates, supporting
    Federer 3.2.28(2),(4), pp. 264,267. The inverse
    laws identify the exact intersection, with no extension
    or arbitrary values outside the image. *)
Theorem homeomorphism_relative_open_images (X Y:topologicalType)
    (f:X->Y) (g:Y->X) (A W:set X):
  is_homeomorphism_with_inverse f g ->relatively_open_set A W ->
  relatively_open_set (f @` A) (f @` W).
Proof.
move=>hH [O [hO hW]].
exists (f @` O); split; first exact:(@homeomorphism_with_inverse_open_map X Y f g hH O hO).
rewrite hW; apply/seteqP; split=>y.
- move=>[x [hAx hOx] <-]; split; by exists x.
- move=>[[x hx hxy] [z hz hzy]].
  have he:x=z:=can_inj (homeomorphism_left_inverse hH) (eq_trans hxy (esym hzy)).
  exists x; last exact hxy.
  split=>//; by rewrite he.
Qed.
