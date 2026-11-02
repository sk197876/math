(** Federer (1969), 3.1.18, pp. 229–230: open neighbourhoods and
    inverse images used in the local changes of coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP
  NormClassZeroComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_full_domain_interior]: the whole ambient space
    is open, supporting linear chart maps in Federer 3.1.18, p. 229. *)
Lemma norm_full_domain_interior (R:realType) (X:lmodType R) (NX:X->R) a :
  norm_domain_interior NX setT a.
Proof. exists 1; split; first exact: ltr01; by move=>h hh. Qed.

(** Source for [norm_open_ball_domain_interior]: norm balls are open
    neighbourhoods, supporting the shrinking in 3.1.18, p. 229. *)
Lemma norm_open_ball_domain_interior (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) c r a : NX (a-c)<r ->
  norm_domain_interior NX (fun x=>NX (x-c)<r) a.
Proof.
move=>ha; exists (r-NX (a-c)); split; first by rewrite subr_gt0.
move=>h hh.
have he : a+h-c=(a-c)+h by rewrite addrAC.
rewrite he; apply: le_lt_trans (real_seminorm_triangle hNX.1 _ _) _.
by lra.
Qed.

(** Source for [norm_class_zero_preimage_interior]: an inverse image
    of an open domain under a globally continuous map is open,
    supporting p inverse(V) in Federer 3.1.18, p. 230. *)
Lemma norm_class_zero_preimage_interior (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R) (B:Y->Prop) (f:X->Y) (g:Y->Z) :
  norm_class_zero NX NY setT f -> norm_class_zero NY NZ B g ->
  forall a, B (f a) -> norm_domain_interior NX (fun x=>B (f x)) a.
Proof.
move=>hf hg a ha.
have [r [hr hball]] := @norm_class_zero_composite_interior R X Y Z NX NY NZ
  setT B f g hf hg a (conj I ha).
exists r; split=>// h hh; exact: (hball h hh).2.
Qed.
