(** Federer (1969), 3.4.2(6), p. 312: laws of the projection retraction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanProjectionSpace
  CriticalManifoldFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_projection_injective]: the univalence
    required in 3.4.2(3), p. 310, follows from the left inverse. This
    supports the retraction used in the proof of (6), p. 312. *)
Lemma critical_chart_projection_injective (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g:
  is_critical_manifold_chart k Z S p g ->
  forall x y,S x ->S y ->
    euclidean_projection_linear p x=euclidean_projection_linear p y ->x=y.
Proof.
move=>h x y hx hy he.
by rewrite -(critical_chart_left_inverse h hx) -(critical_chart_left_inverse h hy) he.
Qed.

(** Source for [critical_chart_inverse_image]: the inverse takes the
    whole original p(S) onto S, 3.4.2(3), p. 310. This proves the exact
    image of the retraction in the proof of (6), p. 312. *)
Lemma critical_chart_inverse_image (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g:
  is_critical_manifold_chart k Z S p g ->
  g @` (euclidean_projection_linear p @` S)=S.
Proof.
move=>h;apply/seteqP;split.
- move=>x [u hu <-];exact:(critical_chart_right_inverse h hu).1.
- move=>x hx;exists (euclidean_projection_linear p x).
  + by exists x.
  + by rewrite (critical_chart_left_inverse h hx).
Qed.

(** Source for [critical_chart_retraction_displacement]: r(x)-x lies
    in ker p and hence in Z, the first display of the proof of
    3.4.2(6), p. 312. The argument uses the original inverse chart. *)
Lemma critical_chart_retraction_displacement (R:realType) m mu k Z S
    (p:euclidean_projection_space R m mu) g:
  is_critical_manifold_chart k Z S p g ->
  forall x,(euclidean_projection_linear p @` S) (euclidean_projection_linear p x) ->
    S (g (euclidean_projection_linear p x)) /\
    Z (g (euclidean_projection_linear p x)-x).
Proof.
move=>h x hx.
have [hS hp]:=critical_chart_right_inverse h hx.
split;first exact:hS.
apply:(critical_chart_kernel h).
by rewrite linearB hp subrr.
Qed.
