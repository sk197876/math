(** Federer (1969), 3.1.1, p. 210: composition preserves class one.
    The proof uses the chain rule and continuity in operator norm,
    with all maps restricted to their actual composite domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLocal NormDifferentialChain NormClassOneUP NormClassOneLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_composite_field]: the sentence asserting
    that compositions of class-one maps are of class one, Federer 3.1.1,
    p. 210. The differential field is the pointwise composite given by
    (2), and its continuity follows from uniform evaluation bounds. *)
Theorem norm_class_one_composite_field (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> Z)
    (D : X -> Hom X Y) (E : Y -> Hom Y Z) :
  is_norm_class_one_field NX NY A f D ->
  is_norm_class_one_field NY NZ B g E ->
  is_norm_class_one_field NX NZ (fun x => A x /\ B (f x))
    (fun x => g (f x)) (fun x => hom_comp (E (f x)) (D x)).
Proof.
move=> hf hg.
have hd : forall a, A a /\ B (f a) ->
    has_norm_differential NX NZ (fun x => A x /\ B (f x))
      (fun x => g (f x)) a (hom_comp (E (f a)) (D a)).
  move=> a [ha hb]; exact: (norm_differential_chain hNX hNY hNZ
    (norm_class_one_differential hf ha) (norm_class_one_differential hg hb)).
constructor=> //.
- exact: (norm_everywhere_differentiable_class_zero hNZ hd).
- move=> a [ha hb] e he.
  have [C [hC hDa]] := norm_differential_bounded (norm_class_one_differential hf ha).
  have [F [hF hEa]] := norm_differential_bounded (norm_class_one_differential hg hb).
  pose p := Num.min 1 (e/(F+C+1)).
  have hden : 0 < F+C+1 by lra.
  have hp : 0 < p by rewrite /p lt_min ltr01 divr_gt0.
  have hp1 : p <= 1 by rewrite /p ge_min lexx.
  have hpe : p <= e/(F+C+1) by rewrite /p ge_min lexx orbT.
  have [r [hr hD]] := norm_class_one_continuity hf ha hp.
  have [s [hs hE]] := norm_class_one_continuity hg hb hp.
  have [t [ht hft]] := norm_differential_continuous_at hNY
    (norm_class_one_differential hf ha) hs.
  exists (Num.min r t); split; first by rewrite lt_min hr ht.
  move=> h [hah hbh] hh v.
  have hmr : Num.min r t <= r by rewrite ge_min lexx.
  have hmt : Num.min r t <= t by rewrite ge_min lexx orbT.
  have hdf := hD h hah (lt_le_trans hh hmr).
  have hsmall := hft h hah (lt_le_trans hh hmt).
  have hshift : f a+(f (a+h)-f a) = f (a+h) by rewrite addrC subrK.
  have hbin : B (f a+(f (a+h)-f a)) by rewrite hshift.
  have heg := hE (f (a+h)-f a) hbin hsmall; rewrite hshift in heg.
  have hEbound : forall w, NZ (E (f (a+h)) w) <= (F+1)*NY w.
    move=> w.
    have heq : E (f (a+h)) w = (E (f (a+h))-E (f a)) w+E (f a) w.
      change (E (f (a+h)) w = (E (f (a+h)) w-E (f a) w)+E (f a) w).
    by rewrite subrK.
    rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNZ.1 _ _) _.
    apply: le_trans (lerD (heg w) (hEa w)) _.
    have hn := real_seminorm_nonnegative hNY.1 w; by nra.
  have heq : (hom_comp (E (f (a+h))) (D (a+h))-hom_comp (E (f a)) (D a)) v =
      E (f (a+h)) ((D (a+h)-D a) v)+(E (f (a+h))-E (f a)) (D a v).
    change (E (f (a+h)) (D (a+h) v)-E (f a) (D a v) =
      E (f (a+h)) (D (a+h) v-D a v)+(E (f (a+h)) (D a v)-E (f a) (D a v))).
    by rewrite linearB /= addrA subrK.
  rewrite heq; apply: le_trans (real_seminorm_triangle hNZ.1 _ _) _.
  have hf0 : 0 <= F+1 by lra.
  have hfirst : NZ (E (f (a+h)) ((D (a+h)-D a) v)) <= (F+1)*(p*NX v).
    apply: le_trans (hEbound _) _; apply: ler_wpM2l=> //; exact: hdf.
  have hsecond : NZ ((E (f (a+h))-E (f a)) (D a v)) <= p*(C*NX v).
    apply: le_trans (heg _) _; apply: ler_wpM2l; first exact: ltW hp.
    exact: hDa.
  apply: le_trans (lerD hfirst hsecond) _.
  have hcoef : p*(F+C+1) <= e by move: hpe; rewrite ler_pdivlMr.
  have hn := real_seminorm_nonnegative hNX.1 v.
  have hhcoef := ler_wpM2r hn hcoef; by nra.
Qed.

(** Source for [norm_class_one_composition]: the intrinsic existential
    form of the composition assertion in Federer 3.1.1, p. 210. *)
Theorem norm_class_one_composition (R : realType) (X Y Z : lmodType R)
    (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (A : X -> Prop) (B : Y -> Prop) (f : X -> Y) (g : Y -> Z) :
  norm_class_one NX NY A f -> norm_class_one NY NZ B g ->
  norm_class_one NX NZ (fun x => A x /\ B (f x)) (fun x => g (f x)).
Proof.
move=> [D hD] [E hE]; exists (fun x => hom_comp (E (f x)) (D x)).
exact: (@norm_class_one_composite_field R X Y Z NX NY NZ hNX hNY hNZ A B f g D E hD hE).
Qed.
