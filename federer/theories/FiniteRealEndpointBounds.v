(** Federer (1969), 3.2.41, printed p. 277: finitely many
    bounded coordinate intervals have common exterior endpoints.
    This supporting finite-sum bound includes the empty family. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_real_endpoint_bounds]: supporting exterior
    coordinate cuts for the intermediate-value step and boundedness
    of the finite box sums in Federer 3.2.41, p. 277. The sum
    of absolute endpoint values supplies local bounds; no global
    extremum or selected endpoint is introduced. *)
Lemma finite_real_endpoint_bounds (R:realType) (I:finType) (a b:I->R):
  exists l u:R,l<u /\forall i,l<=a i /\b i<=u.
Proof.
pose M:R:=\sum_i (`|a i|+`|b i|).
have hEach i:0<=`|a i|+`|b i| by apply:addr_ge0; exact:normr_ge0.
have hM:0<=M by apply:sumr_ge0=> i _; exact:hEach.
have hPart i:`|a i|+`|b i|<=M.
  rewrite /M (bigD1 i) //= lerDl.
  apply:sumr_ge0=> j _; exact:hEach.
exists (-M-1),(M+1); split; first by lra.
move=> i.
have hA:`|a i|<=M.
  apply:le_trans _ (hPart i); by rewrite lerDl normr_ge0.
have hB:`|b i|<=M.
  apply:le_trans _ (hPart i); by rewrite lerDr normr_ge0.
have /andP[hLow _]:(-M<=a i<=M) by rewrite -ler_norml.
have /andP[_ hHigh]:(-M<=b i<=M) by rewrite -ler_norml.
split; lra.
Qed.
