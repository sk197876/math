(** Federer (1969), 3.1.11, pp. 220–221:
    continuity rules supporting the classes of sums,
    scalar multiples, polynomials and Taylor jets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_add]: continuity of
    addition on an open domain, supporting the
    class-k polynomial assertions in Federer 3.1.11,
    pp. 220–221. *)
Lemma norm_class_zero_add (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (f g : X->Y) :
  norm_class_zero NX NY A f -> norm_class_zero NX NY A g ->
  norm_class_zero NX NY A (fun x=>f x+g x).
Proof.
move=> hf hg a ha; split; first exact: (hf a ha).1.
move=> e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [r [hr hrf]] := (hf a ha).2 _ he2.
have [s [hs hsg]] := (hg a ha).2 _ he2.
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=> h hh; rewrite lt_min=> /andP [hhr hhs].
have hid : (f (a+h)+g (a+h))-(f a+g a)=
  (f (a+h)-f a)+(g (a+h)-g a).
  by rewrite opprD addrACA.
rewrite hid; apply: le_lt_trans (real_seminorm_triangle hNY.1 _ _) _.
have hb := ltrD (hrf h hh hhr) (hsg h hh hhs).
have hsum : e/2+e/2=e by lra.
by rewrite hsum in hb.
Qed.

(** Source for [norm_class_zero_scale]: continuity of
    scalar multiplication, including scalar zero, supporting
    polynomial differentiation in Federer 3.1.11, p. 221. *)
Lemma norm_class_zero_scale (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) (c : R) :
  norm_class_zero NX NY A f ->
  norm_class_zero NX NY A (fun x=>c*:f x).
Proof.
move=> hf a ha; split; first exact: (hf a ha).1.
move=> e he.
have hc := normr_ge0 c.
have hp : 0<`|c|+1 by lra.
have hep : 0<e/(`|c|+1) by rewrite divr_gt0.
have [d [hd hdf]] := (hf a ha).2 _ hep.
exists d; split=> // h hh hs.
rewrite -scalerBr (real_seminorm_scale hNY.1).
have hb := hdf h hh hs.
have hz := real_seminorm_nonnegative hNY.1 (f (a+h)-f a).
have hid : (e/(`|c|+1))*(`|c|+1)=e by rewrite divfK // gt_eqF.
nra.
Qed.


(** Source for [norm_class_zero_constant]:
    constant functions on open domains are class
    zero, supporting the Taylor jets and polynomial
    classes in Federer 3.1.11, pp. 220–221. *)
Lemma norm_class_zero_constant (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (c : Y) :
  (forall a, A a -> norm_domain_interior NX A a) ->
  norm_class_zero NX NY A (fun _=>c).
Proof.
move=> hA a ha; split; first exact: hA a ha.
move=> e he; exists 1; split; first exact: ltr01.
by move=> h hh hs; rewrite subrr (real_seminorm_zero hNY.1).
Qed.

(** Source for [norm_class_zero_subtract]:
    continuity of differences on their common open
    domain, supporting the highest-derivative difference
    in Federer 3.1.11, pp. 220–221. *)
Lemma norm_class_zero_subtract (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : X->Prop) (f g : X->Y) :
  norm_class_zero NX NY A f -> norm_class_zero NX NY A g ->
  norm_class_zero NX NY A (fun x=>f x-g x).
Proof.
move=> hf hg.
have hn := norm_class_zero_scale hNY (-1) hg.
have hs := norm_class_zero_add hNY hf hn.
have hid : (fun x=>f x+(-1)*:g x)=(fun x=>f x-g x).
  apply: funext=>x; by rewrite scaleN1r.
by rewrite hid in hs.
Qed.
