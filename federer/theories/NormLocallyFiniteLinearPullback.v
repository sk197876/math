(** Federer (1969), 4.1.1, p. 345: pull the locally
    finite partition of 3.1.13 back through bounded linear
    coordinates. This supports the general finite normed source
    without repeating the Euclidean partition construction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormLinearDomainLaws NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_locally_finite_linear_pullback]: local
    finiteness of a function family is preserved by bounded
    linear precomposition, supporting the original finite-source
    partition in Federer 4.1.1, p. 345, from 3.1.13, p. 225. *)
Theorem norm_locally_finite_linear_pullback (R:realType)
    (X Z:lmodType R) (Y:zmodType) (J:choiceType)
    (NX:X->R) (NZ:Z->R) (hNX:is_real_norm NX)
    (A:Z->Prop) (I:J->Prop) (v:J->Z->Y) (p:Hom X Z):
  norm_bounded_linear NX NZ p ->
  is_norm_locally_finite_function_family NZ A I v ->
  is_norm_locally_finite_function_family NX (fun x=>A (p x)) I (fun s x=>v s (p x)).
Proof.
move=>hp hv x hx.
have [O [hOx [hOA [hOpen [F [hFI hF]]]]]]:=hv (p x) hx.
exists (fun y=>O (p y)); split=>//.
split; first by move=>y hy; exact:hOA (p y) hy.
split.
- move=>y hy; exact:(norm_bounded_linear_preimage_interior hNX hp (hOpen (p y) hy)).
- exists F; split=>// y hy s hs hn; exact:hF (p y) hy s hs hn.
Qed.
