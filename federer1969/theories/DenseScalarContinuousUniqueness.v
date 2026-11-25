(** Federer (1969), 2.6.6, p. 120: uniqueness of the continuous extension
    from the dense union L, without assuming an a priori Lipschitz bound for
    the other extension. This is elementary norm-topology infrastructure
    supporting the printed claim. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ScalarLipschitzExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_scalar_continuous_on_set]: the usual
    epsilon-delta continuity for the uniform norm used in
    Federer 2.6.6, p. 120; stated abstractly for a distance
    on a prescribed domain. *)
Definition is_scalar_continuous_on_set (R : realType) (T : Type)
    (W : set T) (d : T -> T -> R) (A : T -> R) :=
  forall x, W x -> forall e : R, 0<e -> exists t : R,
    0<t /\ forall y, W y -> d x y<t -> `|A x-A y|<e.

(** Source for [scalar_lipschitz_implies_continuous]: the bound
    |gamma|<=nu supplies continuity in Federer 2.6.6,
    p. 120; this is its elementary distance form. *)
Lemma scalar_lipschitz_implies_continuous (R : realType) (T : Type)
    (W : set T) (d : T -> T -> R) (A : T -> R) :
  is_scalar_lipschitz_on_set W d A -> is_scalar_continuous_on_set W d A.
Proof.
move=> h x hx e he; exists e; split=> // y hy hxy.
exact: le_lt_trans (h x y hx hy) hxy.
Qed.

(** Source for [dense_scalar_continuous_unique]: uniqueness of
    the continuous extension in Federer 2.6.6, p. 120.
    Linearity and a common Lipschitz constant are unnecessary
    for this supporting uniqueness theorem. *)
Theorem dense_scalar_continuous_unique (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (A B : T -> R) :
  (forall x, D x -> W x) -> is_pseudometric_dense_subset W D d ->
  is_scalar_continuous_on_set W d A -> is_scalar_continuous_on_set W d B ->
  (forall x, D x -> A x=B x) -> forall x, W x -> A x=B x.
Proof.
move=> hDW hden hA hB heq x hx.
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [a [ha hca]] := hA x hx (e/2) he2.
have [b [hb hcb]] := hB x hx (e/2) he2.
have hab : 0<Order.min a b by rewrite lt_min ha hb.
have [y [hy hxy]] := hden x hx _ hab.
move: hxy; rewrite lt_min=> /andP[hya hyb].
have hva := hca y (hDW y hy) hya.
have hvb := hcb y (hDW y hy) hyb.
rewrite -(heq y hy) in hvb.
have hsum := ltrD hva hvb.
rewrite -splitr in hsum.
apply: le_trans (ler_distD (A y) (A x) (B x)) _; apply: ltW.
have hr : `|A y-B x|=`|B x-A y| by rewrite -opprB normrN.
by rewrite hr; exact: hsum.
Qed.
