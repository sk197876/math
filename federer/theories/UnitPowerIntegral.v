(** Federer (1969), 3.2.13, p. 250: the
    radial integral of r^(m-1) on (0,1)
    is 1/m. This supporting polynomial
    calculation uses the project's finite-increment primitive
    laws and scalar Lebesgue/Riemann identification. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal
  topology normedtype realfun lra ring.
From Federer Require Import UniformPrimitiveUP UniformPrimitiveAlgebra UniformPrimitiveProduct UniformPrimitiveIntegral
  StieltjesIntegral LebesgueScalarMeasure LebesgueRiemannContinuous MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_identity_uniform_primitive]: the
    elementary identity primitive supporting the radial
    power integral in Federer 3.2.13, p. 250. *)
Lemma scalar_identity_uniform_primitive (R:realType) (a b:R):
  is_uniform_primitive_on (fun _:R=>1) (fun x:R=>x) a b.
Proof.
move=>e he; exists 1; split=>// s u t _ hsu hut _ _.
rewrite mul1r subrr normr0; apply:mulr_ge0; first exact:ltW he.
rewrite subr_ge0; exact:le_trans hsu hut.
Qed.

(** Source for [natural_power_uniform_primitive]: the finite
    polynomial primitive underlying the radial normalization
    in Federer 3.2.13, p. 250,
    proved by the existing product rule. *)
Lemma natural_power_uniform_primitive (R:realType) n (a b:R):
  is_uniform_primitive_on (fun x:R=>n.+1%:R*x^+n) (fun x:R=>x^+n.+1) a b.
Proof.
elim:n=>[|n ih].
- apply:(uniform_primitive_ext _ (scalar_identity_uniform_primitive a b))=>x _.
  by rewrite expr0 expr1 mulr1.
- have hC1:continuous (fun _:R=>1:R) by move=>x; exact:cst_continuous.
  have hId:continuous (fun x:R=>x) by move=>x; exact:cvg_id.
  have hCoef:continuous (fun x:R=>n.+1%:R*x^+n).
    move=>x; apply:(@continuousM R R (fun _=>n.+1%:R) (fun y=>y^+n) x).
    + exact:cst_continuous.
    + exact:exprn_continuous.
  have hPow:continuous (fun x:R=>x^+n.+1) by move=>x; exact:exprn_continuous.
  have hProd:=uniform_primitive_product hC1 hId hCoef hPow
    (scalar_identity_uniform_primitive a b) ih.
  apply:(uniform_primitive_ext _ hProd)=>x _; split.
  + rewrite !exprS; set p:=x^+n.
    rewrite -[n.+2%:R]natr1 -[n.+1%:R]natr1; ring.
  + by rewrite [RHS]exprS.
Qed.

(** Source for [unit_natural_power_integral]: the exact
    integral of r^(m-1) over the unit
    radius range in Federer 3.2.13, p. 250,
    expressed with m=n+1 to retain positivity. *)
Lemma unit_natural_power_integral (R:realType) n:
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun x:R=>x^+n)) (n.+1%:R^-1)%:E.
Proof.
have hCont:continuous (fun x:R=>x^+n) by move=>x; exact:exprn_continuous.
have hI:=@lebesgue_riemann_continuous_segment R _ 0 1 hCont ltr01.
have hBase:=@natural_power_uniform_primitive R n 0 1.
have hScale:=uniform_primitive_scale ((n.+1%:R:R)^-1) hBase.
have hPrimitive:is_uniform_primitive_on (fun x:R=>x^+n)
    (fun x:R=>(n.+1%:R)^-1*x^+n.+1) 0 1.
  apply:(uniform_primitive_ext _ hScale)=>x _; split=>//.
  by rewrite mulrA mulVf ?mul1r // pnatr_eq0.
have hValue:=uniform_primitive_riemann_integral hCont ler01 hPrimitive.
rewrite expr1n expr0n /= mulr1 mulr0 subr0 in hValue.
by rewrite -hValue in hI.
Qed.
