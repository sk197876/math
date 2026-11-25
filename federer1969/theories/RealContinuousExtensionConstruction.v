(** Private general-topology proof of the unbounded Tietze theorem
    explicitly invoked in Federer (1969), 2.3.6, p. 77. Source context:
    TietzeNormalisation.v. The numfun import is used only for bounded Tietze
    extension and Urysohn separation; both are general-topology background,
    not measure theorems. We prove the reduction to unbounded functions
    locally using two bounded extensions and a strictly positive
    denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology normedtype numfun.
From Federer Require Import TietzeNormalisation RealContinuousExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [normal_real_continuous_extension_exists]: existence
    theorem cited as Tietze in Federer 2.3.6, p. 77.
    Extend 1/(1+|f|) and f/(1+|f|) boundedly; a Urysohn
    correction makes the first denominator positive everywhere
    without changing it on the closed set C. *)
Theorem normal_real_continuous_extension_exists (R : realType) (X : topologicalType)
    (hn : normal_space X) (C : set X) (hC : closed C) (f : X -> R^o) :
  {within C, continuous f} -> exists h : X -> R^o, is_real_continuous_extension C f h.
Proof.
move=> hf; pose u x := (1 + `|f x|)^-1; pose v x := f x * u x.
have hu x : 0 < u x /\ `|u x| <= 1 := tietze_reciprocal_normalisation_bound (f x).
have hv x : `|v x| <= 1 := tietze_signed_normalisation_bound (f x).
have hucts : {within C, continuous u}.
  move=> x; change ({for x, continuous (fun z : subspace C => ((1 + `|f z|)^-1 : R^o))}).
  apply: (@continuousV R (subspace C) (fun z => 1 + `|f z|) x).
  - exact: lt0r_neq0 (tietze_positive_denominator (f x)).
  - apply: (@continuousD R R^o (subspace C) (fun _ => 1) (fun z => `|f z|) x); first exact: cvg_cst.
    exact: cvg_norm (hf x).
have hvcts : {within C, continuous v}.
  move=> x; rewrite /v; apply: (@continuousM R (subspace C) f u x); [exact: hf x|exact: hucts x].
have [b [hbC hbcts hbbound]] := @continuous_bounded_extension X R hn C hC u 1 ltr01 hucts
  (fun x _ => (hu x).2).
have [k [hkC hkcts hkbound]] := @continuous_bounded_extension X R hn C hC v 1 ltr01 hvcts
  (fun x _ => hv x).
pose Z := [set x | b x = 0].
have hZ : closed Z.
  apply: (@preimage_closed X R^o b [set 0]); first by move=> x _; exact: hbcts x.
  exact: compact_closed (@norm_hausdorff R R^o) (@compact_set1 R^o 0).
have hdis : C `&` Z = set0.
  apply/seteqP; split=> [x [hx hz]|x []].
  have hbx : b x = u x := esym (hbC x (mem_set hx)).
  have hp := (hu x).1; by rewrite -hbx hz ltxx in hp.
have [w [hwcts hwC hwZ hwbound]] := @urysohn_ext_itv X R hn C Z 0 1 hC hZ hdis ltr01.
have hw0 x : C x -> w x = 0.
  move=> hx; apply: hwC; by exists x.
have hw1 x : Z x -> w x = 1.
  move=> hx; apply: hwZ; by exists x.
have hwn x : 0 <= w x.
  have hh := hwbound (w x) (ltac:(by exists x)).
  by move: hh; rewrite set_itvcc /= => /andP[].
pose d x := `|b x| + w x.
have hd x : 0 < d x.
  case: (eqVneq (b x) 0)=> hb.
  - by rewrite /d hb normr0 add0r (hw1 x hb) ltr01.
  - have hbn : 0 < `|b x| by rewrite normr_gt0.
    apply: lt_le_trans hbn _; by rewrite /d lerDl.
have hdcts : continuous d.
  move=> x; rewrite /d; apply: (@continuousD R R^o X (fun z => `|b z|) w x); last exact: hwcts x.
  exact: cvg_norm (hbcts x).
exists (fun x => k x / d x); split.
- move=> x; apply: (@continuousM R X k (fun z => (d z)^-1) x); first exact: hkcts x.
  apply: (@continuousV R X d x); first exact: lt0r_neq0 (hd x).
  exact: hdcts x.
- move=> x hx.
  have hbx : b x = u x := esym (hbC x (mem_set hx)).
  have hkx : k x = v x := esym (hkC x (mem_set hx)).
  rewrite hkx /d hbx (hw0 x hx) addr0 ger0_norm; last exact: ltW (hu x).1.
  rewrite /v mulrK //; rewrite unitfE; exact: lt0r_neq0 (hu x).1.
Qed.
