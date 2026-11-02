(** Federer (1969), 3.1.24, p. 240: analytic
    affine and quadratic scalar expressions in the explicit
    inverse of the rational majorant. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticDomain NormAnalyticArithmetic
  NormAnalyticArithmeticLocal NormAnalyticComposition ScalarPowerAnalytic AnalyticConstantTermCorrection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_affine_analytic_at]: affine scalar
    maps are analytic, supporting the numerator and discriminant
    in Federer 3.1.24, p. 240. The constant coefficient
    and a zero slope are unrestricted. *)
Lemma scalar_affine_analytic_at (R:realType) (b c a:R) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) setT (fun x=>b*x+c) a.
Proof.
pose hN:=scalar_absolute_value_norm R.
have hid:=@scalar_power_analytic_at R 1%N a.
have hscale:=@norm_analytic_at_scale R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN setT
  (fun x=>x^+1) a b hid.
have hconst:=@scalar_constant_analytic_at R c a.
have hsum:=@norm_analytic_at_common_domain_add R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN setT
  (fun x=>b*:x^+1) (fun _=>c) a hscale hconst.
apply: (@norm_analytic_at_domain_agreement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  setT (fun x=>b*:x^+1+c) (fun x=>b*x+c) a _ hsum).
by move=>x _; rewrite expr1.
Qed.

(** Source for [scalar_shifted_square_analytic_at]: the
    shifted square minus a scalar constant in the discriminant
    of Federer's inverse formula is analytic, 3.1.24,
    p. 240. Its whole real domain is retained. *)
Lemma scalar_shifted_square_analytic_at (R:realType) (b d a:R) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) setT (fun x=>(x-b)^+2-d) a.
Proof.
pose hN:=scalar_absolute_value_norm R.
have hAff:=@scalar_affine_analytic_at R 1 (-b) a.
have hSq:=@scalar_power_analytic_at R 2%N (1*a+-b).
have hComp:=@norm_analytic_at_composition R R^o R^o R^o
  (fun t=>`|t|) (fun t=>`|t|) (fun t=>`|t|) hN hN hN setT setT
  (fun x=>1*x+-b) (fun x=>x^+2) a hAff hSq.
have hWhole:=@norm_analytic_at_domain_enlargement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  (fun x=>setT x /\ setT ((fun x=>1*x+-b) x)) setT (fun x=>(1*x+-b)^+2) a
  (fun x hx=>Logic.I) hComp.
have hConst:=@scalar_constant_analytic_at R d a.
have hs:=@norm_analytic_at_subtract R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN setT
  (fun x=>(1*x+-b)^+2) (fun _=>d) a hWhole hConst.
apply: (@norm_analytic_at_domain_agreement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  setT (fun x=>(1*x+-b)^+2-d) (fun x=>(x-b)^+2-d) a _ hs).
by move=>x _; rewrite mul1r.
Qed.
