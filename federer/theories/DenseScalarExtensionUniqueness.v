(** Federer (1969), 2.5.9, p. 100: uniqueness of the continuous extension
    from a dense domain. The positive density is corrected by erratum p. 2,
    book p. 100 line 22. This abstract pseudometric uniqueness argument is
    supporting infrastructure, not a separately numbered source claim. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ScalarLipschitzExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_scalar_lipschitz_extension_unique]: uniqueness in the
    continuous-extension step of Federer 2.5.9, p. 100 *)
Theorem dense_scalar_lipschitz_extension_unique (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (A B C : T -> R) :
  is_pseudometric_on_set W d -> (forall x, D x -> W x) -> is_pseudometric_dense_subset W D d ->
  is_scalar_lipschitz_extension W D d A B ->
  is_scalar_lipschitz_extension W D d A C ->
  forall x, W x -> B x=C x.
Proof.
move=> [hd0 [hdiag [hsym htri]]] hDW hd [hBA hB] [hCA hC] x hx.
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he2 : 0 < e/2 by rewrite divr_gt0 // ltr0n.
have [y [hy hxy]] := hd x hx (e/2) he2.
have hb := hB x y hx (hDW y hy).
have hc := hC y x (hDW y hy) hx.
rewrite (hsym y x (hDW y hy) hx) (hCA y hy) -(hBA y hy) in hc.
have hh := le_trans (ler_distD (B y) (B x) (C x)) (lerD hb hc).
apply: le_trans hh _; apply: ltW.
have h := ltrD hxy hxy; by rewrite -splitr in h.
Qed.
