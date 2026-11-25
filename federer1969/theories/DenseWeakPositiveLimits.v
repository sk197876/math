(** Federer (1969), 4.1.5, p. 350:
    the last sentence of the ball quotient
    argument. Uniformly bounded linear functions
    converge on every target vector if they
    converge on a dense set. This supplies
    the stated simultaneous quantifier, without
    separability of the dual. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring lra.
From Federer Require Import Hom RealNormUP NormMetric VectorDaniellDualExtension PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dense_bounded_weak_positive_limit]: the
    dense-set extension in the ball quotient formula
    of Federer 4.1.5, p. 350. The
    original functionals have their unit dual bound. *)
Theorem dense_bounded_weak_positive_limit (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (C:set (real_norm_metric_space hNY))
    (A:R->Hom Y R^o) (l:Hom Y R^o) (cap:R):
  dense C ->0<cap ->
  (forall r,0<r ->r<cap ->forall y,`|A r y|<=NY y) ->
  (forall y,`|l y|<=NY y) ->
  (forall y,C y ->@positive_norm_limit R R^o (fun z:R=>`|z|) (fun r=>A r y) (l y)) ->
  forall y,@positive_norm_limit R R^o (fun z:R=>`|z|) (fun r=>A r y) (l y).
Proof.
move=>hDense hCap hBound hLimitBound hDenseLimit y epsilon hEpsilon.
have hThird:0<epsilon/3 by rewrite divr_gt0 // ltr0n.
have[z [hZ hNear]]:=@dense_approximation R Y NY hNY C hDense y (epsilon/3) hThird.
have[d [hD hClose]]:=hDenseLimit z hZ (epsilon/3) hThird.
exists (Num.min cap d); split; first by rewrite lt_min hCap hD.
move=>r hR hSmall.
have /andP [hRCap hRD]:(r<cap)&&(r<d) by move:hSmall; rewrite lt_min.
have hMiddle:=hClose r hR hRD.
have hFirst:=hBound r hR hRCap (y-z).
have hLast:=hLimitBound (z-y).
rewrite (real_seminorm_subtract hNY.1) in hLast.
have hSplit:A r y-l y=A r (y-z)+(A r z-l z)+l (z-y).
  by rewrite !linearB; ring.
rewrite hSplit.
have hTriangle:`|A r (y-z)+(A r z-l z)+l (z-y)|<=
    `|A r (y-z)|+`|A r z-l z|+`|l (z-y)| :=
  le_trans (ler_normD _ _) (lerD (ler_normD _ _) (lexx _)).
apply:le_lt_trans hTriangle _.
lra.
Qed.
