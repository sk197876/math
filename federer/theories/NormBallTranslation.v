(** Federer (1969), 3.1.19, p. 231: translations supply the local
    zero-dimensional straightening maps. They are diffeomorphisms of
    every class on the corresponding open norm balls. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations NormOpenDomainLaws NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_ball_translation_diffeomorphism]: supporting the
    isolated-point charts in the last sentence of Federer 3.1.19,
    p. 231. The inverse translations have the actual ball domains;
    every finite class, including zero, is covered. *)
Theorem norm_ball_translation_diffeomorphism (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) b r k :
  is_norm_diffeomorphism hNX hNX (fun x=>NX (x-b)<r) (fun y=>NX (y-0)<r)
    (fun x=>x-b) (fun y=>y+b) k.
Proof.
pose A:=fun x=>NX (x-b)<r.
pose C:=fun y=>NX (y-0)<r.
have hA x (hx:A x):norm_domain_interior NX A x.
  exact (@norm_open_ball_domain_interior R X NX hNX b r x hx).
have hC y (hy:C y):norm_domain_interior NX C y.
  exact (@norm_open_ball_domain_interior R X NX hNX 0 r y hy).
pose I:=hom_of_linear (linear_id X).
have hI:norm_bounded_linear NX NX I.
  exists 1; split; first exact: ler01.
  by move=>x; change (NX x<=1*NX x); rewrite mul1r.
have hcI:=@norm_class_linear R X X NX NX hNX hNX A I k hA hI.
have hcB:=@norm_class_constant R X X NX NX hNX hNX A b k hA.
have hforward:=norm_class_subtract hcI hcB.
have hiI:=@norm_class_linear R X X NX NX hNX hNX C I k hC hI.
have hiB:=@norm_class_constant R X X NX NX hNX hNX C b k hC.
have hinverse:=norm_class_add hiI hiB.
constructor=>//.
- exists I,I; split=>//; split=>//; split; by move=>x.
- by move=>x hx; rewrite subr0.
- by move=>y hy; rewrite addrK; move:hy; rewrite subr0.
- by move=>x hx; rewrite subrK.
- by move=>y hy; rewrite addrK.
Qed.
