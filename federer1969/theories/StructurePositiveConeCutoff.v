(** Federer (1969), 3.3.6, pp. 293–294: equivalent
    positive cutoff inequalities, retaining infinity. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_positive_cone_cutoff]: the inequality
    3h <= 6 rho/e = 24 rho/s <= xi in Federer 3.3.6,
    p. 294, when e=s/4. The original printed rho<=s xi/24
    is used literally; positive infinite xi is retained. *)
Theorem structure_positive_cone_cutoff (R:realType) (s rho:R) (xi: \bar R):
  0<s ->(0<xi)%E ->(rho%:E<=s%:E*xi/(24:R)%:E)%E ->
  ((6*rho/(s/4))%:E<=xi)%E.
Proof.
move=>hs; case:xi=>[t| |] hXi hRho; [|exact:leey|].
- rewrite lte_fin in hXi.
  have hTwentyFour:(24:R)!= 0 by rewrite pnatr_eq0.
  rewrite inver (negbTE hTwentyFour) -!EFinM lee_fin in hRho.
  rewrite lee_fin.
  have hScale:6*rho/(s/4)= 24*rho/s by rewrite invfM invrK; ring.
  rewrite hScale ler_pdivrMr //; nra.
- by rewrite ltNge leNye in hXi.
Qed.
