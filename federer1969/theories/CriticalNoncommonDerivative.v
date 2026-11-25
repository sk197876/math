(** Federer (1969), 3.4.2(7), p. 314: a point outside B has
    a genuine nonzero derivative detected by a bounded functional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity RelativeClassUP PartialFunctionUP RelativeDifferential
  SeminormNormingFunctional CriticalFlatPiecesUP CriticalRelativeDifferentialLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_noncommon_derivative_witness]: the choice
    of f, z, and the Hahn–Banach functional at a point of C minus B
    in 3.4.2(7), p. 314. Relative class supplies a genuine derivative;
    failure of its vanishing condition supplies a nonzero value.
    A norming functional detects that value with a positive scalar.
    All witnesses remain local, and no target basis is required. *)
Theorem critical_noncommon_derivative_witness (R:realType) m k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m)) a:
  (1<=k)%N ->C `<=` S ->C a ->
  ~critical_common_tangent_zero_set hNY Z S C k a ->
  exists (f:R_n R m->Y) (L:partial_function (R_n R m) Y) z y (alpha:Hom Y R^o),
    critical_flat_function_class hNY S C f k /\Z z /\
    partial_function_graph (relative_norm_differential
      (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f) a L /\
    partial_function_graph L z y /\y!=0 /\
    norm_bounded_linear NY (fun t:R^o=>`|t|) alpha /\0<alpha y.
Proof.
move=>hk hCS hc hNotB.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
have ha:S a:=hCS a hc.
have [f [hf hNotZero]]:exists f:X->Y,critical_flat_function_class hNY S C f k /\
    ~critical_tangent_zero_locus hNY Z S f a.
  apply:contrapT=>hNo;apply:hNotB;split;first exact:hc.
  move=>f hf;apply:contrapT=>hBad;apply:hNo;by exists f.
have [U [F [haU [hF hAgree]]]]:=hf.1 a ha.
have hF1:=norm_class_lower hk hF.
have [D hD]:=(norm_class_firstP hNX hNY U F).1 hF1.
have hEqual x (hx:S x) (hxU:U x):f x=F x:= (hAgree x hx hxU).2.
have [L [hOuter hValues]]:=@critical_relative_differential_from_extension R X Y
  NX NY hNX hNY U S F f a (D a) ha hEqual (norm_class_one_differential hD haU).
have [z [y [hz [hInner hNonzero]]]]:
    exists z y,Z z /\partial_function_graph L z y /\y!=0.
  apply:contrapT=>hNo;apply:hNotZero;split;first exact:ha.
  exists L;split;first exact:hOuter.
  move=>z y hz hy;case:(eqVneq y 0)=>[hZero|hNonzero];first exact:hZero.
  exfalso;apply:hNo;exists z,y;by repeat split.
have [alpha [hBound hValue]]:=seminorm_norming_functional hNY.1 y.
have hPositive:0<NY y by rewrite (real_norm_positive hNY.1 hNY.2) hNonzero.
exists f,L,z,y,(hom_of_linear alpha).
split;first exact:hf.
split;first exact:hz.
split;first exact:hOuter.
split;first exact:hInner.
split;first exact:hNonzero.
split.
- exists 1;split;first exact:ler01.
  by move=>v;rewrite hom_of_linearE mul1r;exact:hBound.
- by rewrite hom_of_linearE hValue.
Qed.
