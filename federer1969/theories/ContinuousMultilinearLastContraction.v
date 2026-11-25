(** Federer (1969), 3.1.11, pp. 219–221:
    evaluating the final argument is a bounded
    bilinear operation on continuous multilinear maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormOperatorNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearCurrying
  MultilinearArguments NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_last_contraction_exists]:
    contraction with one vector, supporting the
    polynomial derivative identities of Federer
    3.1.11, p. 221, with the
    multilinear norm of p. 219.
    Its norm is at most the product
    of the form norm and vector norm. *)
Theorem continuous_multilinear_last_contraction_exists (R : realType) k
    (X Y P T : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX)
    (ep : {ffun 'I_k->X}->Hom P Y) (PN : P->R)
    (et : {ffun 'I_(k+1)->X}->Hom T Y) (TN : T->R)
    (hP : is_continuous_multilinear_space NX NY ep PN)
    (hT : is_continuous_multilinear_space NX NY et TN) :
  exists C : T->X->P,
    norm_bounded_bilinear TN NX PN C /\
    forall z x u, ep u (C z x)=et (multilinear_arguments_join u [ffun _ : 'I_1=>x]) z.
Proof.
have hf z : norm_bounded_multilinear NX NY (fun u=>et u z).
  split; first exact: continuous_multilinear_evaluation hT z.
  exists (TN z); split.
  - exact: multilinear_operator_nonnegative (continuous_multilinear_norm_laws hT z).
  - exact: multilinear_operator_bound (continuous_multilinear_norm_laws hT z).
have hex z := continuous_multilinear_curry_exists hNX hP (hf z).
have [L hL] := choice hex.
pose C z x := L z x.
have hCE z x u : ep u (C z x)=et (multilinear_arguments_join u [ffun _ : 'I_1=>x]) z.
  exact: (hL z).2.
exists C; split; last exact hCE.
split.
- split.
  + move=>x a z w; apply: (continuous_multilinear_extensional hP)=>u.
    by rewrite (hom_linear (ep u)) !hCE
      (hom_linear (et (multilinear_arguments_join u [ffun _ : 'I_1=>x]))).
  + move=>z; exact: hom_linear.
- exists 1; split; first exact: ler01.
  move=>z x; rewrite mul1r.
  have hn := continuous_multilinear_curry_norm hNX hP
    (continuous_multilinear_norm_laws hT z) (fun u x=>hCE z x u).
  exact: norm_operator_bound hn x.
Qed.
