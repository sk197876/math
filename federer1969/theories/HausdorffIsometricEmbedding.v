(** Federer (1969), 3.2.28(2),(3), pp. 265–266:
    Hausdorff measures of the fibres are unchanged by the
    displayed isometric identifications. Supporting general
    metric lemma from the two image bounds of 2.10.11, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import LipschitzUP HausdorffMeasure HausdorffRestrictedLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_isometric_embedding_invariance]: the
    fibre isometries in Federer 3.2.28(2),(3), pp. 265–266,
    by 2.10.11, p. 176. A left inverse suffices: only
    its restriction to the actual image is used in the
    reverse estimate. All natural degrees and outer measures
    of arbitrary, possibly nonmeasurable sets are covered. *)
Theorem hausdorff_isometric_embedding_invariance (R:realType)
    (X Y:metricType R) (f:X->Y) (g:Y->X):
  cancel f g ->(forall x y,mdist (f x) (f y)=mdist x y) ->
  forall k A,@hausdorff_measure R Y k (f @` A)=@hausdorff_measure R X k A.
Proof.
move=>hgf hdist k A.
have hf:is_metric_lipschitz_bound A f 1%R.
  split; first exact:ler01.
  by move=>x y _ _; rewrite hdist mul1r.
have hg:is_metric_lipschitz_bound (f @` A) g 1%R.
  split; first exact:ler01.
  move=>x y [u hu <-] [v hv <-].
  by rewrite !hgf hdist mul1r.
have hu:=@hausdorff_lipschitz_on_bound R X Y A f 1%R k A hf (fun x (hx:A x)=>hx).
have hl:=@hausdorff_lipschitz_on_bound R Y X (f @` A) g 1%R k (f @` A) hg
  (fun y (hy:(f @` A) y)=>hy).
have hImage:g @` (f @` A)=A.
  apply/seteqP; split.
  - by move=>x [y [z hz <-] <-]; rewrite hgf.
  - move=>x hx; exists (f x); last exact:hgf x.
    by exists x.
rewrite expr1n mul1e in hu.
rewrite hImage expr1n mul1e in hl.
by apply/eqP; rewrite eq_le hu hl.
Qed.
