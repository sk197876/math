(** Federer (1969), 1.8.2, p. 40: translating m <= dim_C V
    into the existence of an independent m-frame. This supporting
    basis restriction works over any field. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom LinearBasis FiniteDualDimension FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [basis_prefix_independent]: Federer 1.8.2,
    p. 40, the dimension hypothesis supplies an independent frame
    by taking the first m vectors of a basis of length n. *)
Theorem basis_prefix_independent (K : fieldType) (V : lmodType K)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (m <= n)%N) :
  finite_independent (fun i : 'I_m => e (widen_ord hm i)).
Proof.
apply: (@finite_independent_separating K (Finite.clone 'I_m _) V
  (fun i => e (widen_ord hm i))
  (fun i => hom_as_linear (dual_basis he (widen_ord hm i)))) => i j.
change (dual_basis he (widen_ord hm i) (e (widen_ord hm j)) =
  if i == j then 1 else 0).
have hw : injective (@widen_ord m n hm).
  move=> u w huw; apply: val_inj; exact (congr1 (@nat_of_ord n) huw).
by rewrite dual_basisE (inj_eq hw) eq_sym.
Qed.
