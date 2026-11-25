(** Federer (1969), 4.1.2, pp. 346–347:
    the exact uniform derivative norm after scalar dilation.
    The scalar argument map is bijective; the earlier
    least-bound norm laws give equality rather than an estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP UniformFunctionNormUP UniformFunctionNormLaws UniformFunctionNormSurjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scaled_argument_exact_uniform_norm]: positive
    scalar dilation and amplitude multiplication give the
    exact factor epsilon^(-n-k), supporting Federer
    4.1.2, pp. 346–347. *)
Theorem scaled_argument_exact_uniform_norm (R:realType) (X Z:lmodType R)
    (NZ:Z->R) (hNZ:is_real_norm NZ) (D:X->Z) n k G e:
  0<e ->is_uniform_function_norm (fun x=>NZ (D x)) G ->
  is_uniform_function_norm (fun x=>NZ ((e^+(n+k))^-1*:D (e^-1*:x))) (G/(e^+(n+k))).
Proof.
move=>he hG.
pose c:=(e^+(n+k))^-1.
have hc:0<c by rewrite /c invr_gt0; exact:exprn_gt0.
have hSurj:forall z:X,exists x:X,e^-1*:x=z.
  move=>z; exists (e*:z); by rewrite scalerA mulVf ?scale1r // gt_eqF.
have hPre:=@uniform_function_norm_surjective_precompose R X X (fun x=>NZ (D x))
  (fun x=>e^-1*:x) G hSurj hG.
have hScale:=@uniform_function_norm_scale R X (fun x=>NZ (D (e^-1*:x))) G c hPre.
have hEq:(fun x=>NZ (c*:D (e^-1*:x)))=(fun x=>c*NZ (D (e^-1*:x))).
  apply:funext=>x; by rewrite (real_seminorm_scale hNZ.1) (ger0_norm (ltW hc)).
have hValue:`|c|*G=G/(e^+(n+k)).
  by rewrite (ger0_norm (ltW hc)) /c mulrC.
rewrite hValue in hScale; rewrite -hEq in hScale; exact hScale.
Qed.
