(** Federer (1969), 3.3.6, pp. 293–294: exact scalar
    factors in the two-cone and packing estimates. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_two_cone_coefficient]: the exact equality
    2 lambda alpha(m) (3h)^m s^m =
    2 (12)^m lambda alpha(m) (e h)^m for s= 4e,
    Federer 3.3.6, p. 294. Every natural degree is retained. *)
Lemma structure_two_cone_coefficient (R:realType) m (lam alpha h e:R):
  (lam*alpha*(3*h)^+m*(4*e)^+m)+
    (lam*alpha*(3*h)^+m*(4*e)^+m)=
    (2*12^+m*lam)*(alpha*(e*h)^+m).
Proof.
have hT:(12:R)= 3*4 by lra.
rewrite hT !exprMn; ring.
Qed.

(** Source for [structure_packing_coefficient]: the exact final
    coefficient 2 times 84 to power m, Federer 3.3.6, p. 293.
    The two-cone factor 12 and packing factor 7 multiply without
    changing the printed unspecified or specified constants. *)
Lemma structure_packing_coefficient (R:realType) m (lam alpha rho:R):
  (2*12^+m*lam)*(7^+m*alpha*rho^+m)=
    2*84^+m*lam*alpha*rho^+m.
Proof.
have hT:(84:R)= 12*7 by lra.
rewrite hT exprMn; ring.
Qed.
