(** Federer (1969), 3.2.46, pp. 281–282: original
    path-distance Lipschitz bounds imply finite-carrier bounds.
    This supporting scalar lemma ensures the technical cap
    introduces no extra hypothesis on the book's maps.
    Original infinite component distances are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealUnitCap ExtendedRealUnitCapOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [extended_real_unit_cap_positive_scale_bound]:
    cap(c z)<=max(1,c) cap(z) for c>0 and z>=0,
    technical support for the original-rho Lipschitz
    reduction of 3.2.46, p. 282. Infinite z is
    included; no original path distance is replaced. *)
Lemma extended_real_unit_cap_positive_scale_bound (R : realType) (c : R) (z : \bar R) :
  0<c -> (0<=z)%E ->
  extended_real_unit_cap (c%:E*z)%E <= Num.max 1 c*extended_real_unit_cap z.
Proof.
move=> hc.
have hC1 : 1<=Num.max 1 c by rewrite le_max lexx.
have hCc : c<=Num.max 1 c by rewrite le_max lexx orbT.
case: z=> [r| |] hz.
- have hr : 0<=r by move: hz; rewrite lee_fin.
  rewrite -EFinM !extended_real_unit_cap_finite.
  case: (leP r 1)=> hSmall.
  + apply: le_trans _ (ler_wpM2r hr hCc).
    by rewrite ge_min lexx.
  + rewrite mulr1; apply: le_trans _ hC1; by rewrite ge_min lexx orbT.
- rewrite mulry (gtr0_sg hc) mul1e !extended_real_unit_cap_posinf mulr1.
  exact hC1.
- by [].
Qed.
