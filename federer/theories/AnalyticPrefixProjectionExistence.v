(** Federer (1969), 3.4.8(1), p. 326:
    the actual finite list of original coordinate
    functionals gives the projection specified by its laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations AnalyticPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_projection_exists]: the
    original coordinate projection exists for every prefix,
    including dimension zero, 3.4.8(1), p. 326.
    The coordinate function is only an existence witness. *)
Theorem analytic_prefix_projection_exists (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) j (hjn:(j<=n)%N):
  exists P:Hom X (R_n R j),is_analytic_prefix_projection omega hjn P.
Proof.
pose f (x:X):R_n R j:=[ffun i=>omega (widen_ord hjn i) x].
have hLinear:linear f.
  move=>a x y;apply/ffunP=>i;rewrite /f !ffunE.
  exact:(hom_linear (omega (widen_ord hjn i)) a x y).
exists (@HomMap R X (R_n R j) f (introT (asboolP _) hLinear))=>x i.
change (f x i=omega (widen_ord hjn i) x).
by rewrite /f ffunE.
Qed.
