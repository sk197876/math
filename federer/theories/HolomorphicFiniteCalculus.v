(** Federer (1969), 3.4.12, p. 339: finite original
    complex polynomial expressions are holomorphic on their actual
    domains. Reuse composition, restriction, constants, addition and products. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals classical_sets.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormDifferentialUP HolomorphicUP HolomorphicOpenDomain HolomorphicRestriction HolomorphicComposition
  HolomorphicArithmetic HolomorphicProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_compose_on]: compose on the original
    prescribed domain, extending the analytic composition laws of
    3.1.24, p. 240, under 3.4.12, pp. 338–339. *)
Lemma holomorphic_compose_on (R:realType) (X Y Z:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    (hNY:is_real_norm (fun y:restricted_space (ComplexScalars.embed R) Y=>NY y))
    (hNZ:is_real_norm (fun z:restricted_space (ComplexScalars.embed R) Z=>NZ z))
    (A:set X) (B:set Y) (f:X->Y) (g:Y->Z):
  (forall x,A x ->B (f x)) ->is_holomorphic hNX hNY A f ->is_holomorphic hNY hNZ B g ->
  is_holomorphic hNX hNZ A (fun x=>g (f x)).
Proof.
move=>hAB hF hG.
have hComposite:=holomorphic_composition hF hG.
apply:(@holomorphic_open_restriction R X Z NX NZ hNX hNZ
  (fun x=>A x /\B (f x)) A (fun x=>g (f x)) _ _ hComposite).
- by move=>x hx;split;[exact:hx|exact:hAB x hx].
- exact:holomorphic_domain_interior hF.
Qed.

(** Source for [holomorphic_finite_sum]: finite sums retain
    holomorphy, including the empty sum, in the original
    finite remainder expression of 3.4.6, p. 323, extended
    by 3.4.12, p. 339. *)
Lemma holomorphic_finite_sum (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R)
    (NY:restricted_space (ComplexScalars.embed R) Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (A:set X) (I:finType) (f:I->X->Y):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,is_holomorphic hNX hNY A (f i)) ->
  is_holomorphic hNX hNY A (fun x=>\sum_i f i x).
Proof.
move=>hOpen hf.
have hSum:is_holomorphic hNX hNY A (\sum_i f i).
  elim/big_ind:_=>[|g h hg hh|i _].
  - exact:(@holomorphic_constant R X Y NX NY hNX hNY A 0 hOpen).
  - exact:holomorphic_add hg hh.
  - exact:hf.
apply:(@holomorphic_domain_agreement R X Y NX NY hNX hNY A
  (\sum_i f i) (fun x=>\sum_i f i x) _ hSum)=>x hx.
by elim/big_rec2:_=>[|i y F _ <-].
Qed.

(** Source for [holomorphic_scalar_power]: each original scalar
    power is holomorphic, including exponent zero, supporting
    the complex preparation polynomial of 3.4.12, p. 339. *)
Lemma holomorphic_scalar_power (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX)
    (A:set X) (f:X->ComplexScalars.C R) m:
  is_holomorphic hNX (@complex_modulus_real_norm R) A f ->
  is_holomorphic hNX (@complex_modulus_real_norm R) A (fun x=>(f x)^+m).
Proof.
move=>hf;elim:m=>[|m ih].
- have hOpen:=holomorphic_domain_interior hf.
  exact:(@holomorphic_constant R X (ComplexScalars.C R)^o NX (@complex_modulus R)
    hNX (@complex_modulus_real_norm R) A 1 hOpen).
- have hProduct:=holomorphic_product hf ih.
  apply:(holomorphic_domain_agreement _ hProduct)=>x _;by rewrite exprS.
Qed.
