(** Federer (1969), 1.8.4, pp. 40-41: either factor may
    be simple. Supporting invariance of mass under interchanging
    wedge factors follows from the graded sign law and absolute
    homogeneity, as in 1.3.1 and 1.8.1. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorAlgebra
  ExteriorAnticommutativity ExteriorHomogeneousProducts GradedComponents
  AlternatingCoordinates ComassUP MassUP MassHomogeneity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [mass_reindex]: Federer 1.8.4, pp. 40-41,
    supporting transport of the dual supremum along equal degree
    indices. Both comass functions obey the same intrinsic laws. *)
Lemma mass_reindex (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    p q (h : p=q) (kp : A_m V R^o p -> R) (kq : A_m V R^o q -> R)
    (hp : forall phi, is_comass h2 hB phi (kp phi))
    (hq : forall phi, is_comass h2 hB phi (kq phi))
    (x : exterior_power V p) c :
  is_mass kp x c -> is_mass kq (exterior_reindex h x) c.
Proof.
case: q / h kq hq => kq hq hc.
have he : kp=kq by apply: funext => phi; exact: comass_unique (hp phi) (hq phi).
by rewrite -he.
Qed.

(** Source for [mass_wedge_swap]: Federer 1.8.4,
    pp. 40-41, interchanging the factors preserves the mass
    of their exterior product. The degree hypothesis matches the
    positive-degree norm convention of 1.8.1. *)
Theorem mass_wedge_swap (R : rcfType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    p q (hm : (0 < p+q)%N)
    (kr : A_m V R^o (p+q) -> R) (ks : A_m V R^o (q+p) -> R)
    (hr : forall phi, is_comass h2 hB phi (kr phi))
    (hs : forall phi, is_comass h2 hB phi (ks phi))
    (x : exterior_power V p) (y : exterior_power V q) c d :
  is_mass kr (exterior_product x y) c ->
  is_mass ks (exterior_product y x) d -> c=d.
Proof.
move=> hc hd.
have he : exterior_reindex (addnC q p) (exterior_product y x) =
    (-1 : R)^+(p*q) *: exterior_product x y.
  apply: val_inj.
  change (component_val (exterior_reindex (addnC q p) (exterior_product y x)) =
    component_val ((-1 : R)^+(p*q) *: exterior_product x y)).
  rewrite exterior_reindexE linearZ !exterior_productE mulnC.
  exact (@exterior_anticommutative R V q p (component_val y) (component_val x)
    (component_homogeneous y) (component_homogeneous x)).
have hd' := @mass_reindex R h2 V B hB (q+p) (p+q) (addnC q p)
  ks kr hs hr (exterior_product y x) d hd.
rewrite he in hd'.
have hh := @mass_absolute_homogeneity R h2 V B hB (p+q) hm kr hr
  (exterior_product x y) ((-1 : R)^+(p*q)) c d hc hd'.
by rewrite normrX normrN normr1 expr1n mul1r in hh; symmetry.
Qed.
