(** Federer (1969), 3.1.24, p. 240: translations used in
    analytic submanifold coordinates are analytic on any open domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormAnalyticUP
  NormAnalyticLinear NormAnalyticConstant NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_translations_analytic]: the affine fibre
    translation in the analytic version of 3.1.19, as stated
    in 3.1.24, p. 240. It is the sum or difference of
    the identity and a constant, with both directions proved. *)
Lemma norm_translations_analytic (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop)
    (hA:forall x,A x -> norm_domain_interior NX A x) (c:X) :
  @norm_analytic R X X NX NX hNX hNX A (fun x=>x+c) /\
  @norm_analytic R X X NX NX hNX hNX A (fun x=>x-c).
Proof.
have hI:norm_bounded_linear NX NX (hom_of_linear (linear_id X)).
  exists 1; split; first exact:ler01.
  by move=>x; rewrite hom_of_linearE mul1r.
have hi:=@norm_bounded_linear_analytic R X X NX NX hNX hNX A hA
  (hom_of_linear (linear_id X)) hI.
have hc:=@norm_constant_analytic R X X NX NX hNX hNX A hA c.
split; [exact (norm_analytic_add hi hc)|exact (norm_analytic_subtract hi hc)].
Qed.
