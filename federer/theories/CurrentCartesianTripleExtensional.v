(** Federer (1969), 4.1.8, p. 361: all original
    triple separated tests determine a current on the
    open three-factor product. Reuse the proved two-factor
    density consequence of 4.1.3, p. 348, twice,
    using the actual continuous partial evaluation currents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentCartesianMixedExtensional
  CurrentCartesianFactorCurrents CurrentCartesianTestDegreeTransport CurrentDegreeTransport
  CurrentDegreeTransportComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianTripleExtensional.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)) (C:set (R_n R v)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Hypothesis hC:forall c,C c->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R v)) C c.
Local Notation BC := (@euclidean_cartesian_set R n v B C).
Local Notation hBC := (@current_cartesian_domain_open R n v B C hB hC).
Local Notation ABC := (@euclidean_cartesian_set R m (n+v) A BC).
Local Notation hABC := (@current_cartesian_domain_open R m (n+v) A BC hA hBC).
Local Notation DA := (fun a=>@current_test_space R h2 m A hA a).
Local Notation DB := (fun b=>@current_test_space R h2 n B hB b).
Local Notation DC := (fun c=>@current_test_space R h2 v C hC c).
Local Notation DBC := (fun b=>@current_test_space R h2 (n+v) BC hBC b).
Local Notation CC := (fun d=>@current_space R h2 (m+(n+v)) ABC hABC d).
Local Notation PureBC := (fun b c=>@CartesianTestProduct.value R h2 n v B C hB hC b c).
Local Notation PureA := (fun a t=>@CartesianTestProduct.value R h2 m (n+v) A BC hA hBC a t).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+(n+v)) ABC hABC a b e).
Local Notation TrBC := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (n+v) BC hBC a b e).
Local Notation CTr := (fun a b (e:a=b)=>@current_degree_transport R h2 (m+(n+v)) ABC hABC a b e).
Local Notation ev := (fun d=>@current_value R h2 (m+(n+v)) ABC hABC d).
Local Notation evBC := (fun t=>@current_value R h2 (n+v) BC hBC t).

(** Source for [current_cartesian_triple_values_extensional]:
    equality on every original triple separated test implies
    equality of arbitrary currents on the open three-factor
    product, supporting associativity in Federer 4.1.8,
    p. 361. The original tensor density is reused
    through proved continuous partial evaluation currents. *)
Theorem current_cartesian_triple_values_extensional d (P Q:CC d):
  (forall a b c (e:(a+(b+c))%N=d) (alpha:DA a) (beta:DB b) (gamma:DC c),
    ev d P (Tr _ _ e (PureA a (b+c) alpha (PureBC b c beta gamma)))=
      ev d Q (Tr _ _ e (PureA a (b+c) alpha (PureBC b c beta gamma))))->P=Q.
Proof.
move=>hTriple.
apply:(@current_cartesian_mixed_values_extensional R h2 m (n+v) A BC hA hBC d P Q).
move=>a t e alpha psi.
pose P0:=CTr _ _ (esym e) P.
pose Q0:=CTr _ _ (esym e) Q.
have[LP hLP]:=@current_cartesian_second_factor_current_exists R h2 m (n+v) A BC hA hBC
  a t P0 alpha.
have[LQ hLQ]:=@current_cartesian_second_factor_current_exists R h2 m (n+v) A BC hA hBC
  a t Q0 alpha.
have hPartial:LP=LQ.
  apply:(@current_cartesian_mixed_values_extensional R h2 n v B C hB hC t LP LQ).
  move=>b c f beta gamma.
  rewrite (hLP (TrBC _ _ f (PureBC b c beta gamma)))
    (hLQ (TrBC _ _ f (PureBC b c beta gamma))).
  cbn beta.
  rewrite (@current_cartesian_test_product_second_transport R h2 m (n+v) A BC hA hBC
    a (b+c) t f alpha (PureBC b c beta gamma)) /P0 /Q0.
  rewrite (@current_degree_reverse_evaluation R h2 (m+(n+v)) ABC hABC (a+t) d e P
    (Tr _ _ (congr1 (addn a) f) (PureA a (b+c) alpha (PureBC b c beta gamma))))
    (@current_degree_reverse_evaluation R h2 (m+(n+v)) ABC hABC (a+t) d e Q
    (Tr _ _ (congr1 (addn a) f) (PureA a (b+c) alpha (PureBC b c beta gamma))))
    !current_test_degree_transport_composition.
  exact:(hTriple a b c (eq_trans (congr1 (addn a) f) e) alpha beta gamma).
have hSame:evBC t LP psi=evBC t LQ psi by rewrite hPartial.
rewrite (hLP psi) (hLQ psi) /P0 /Q0 in hSame.
rewrite (@current_degree_reverse_evaluation R h2 (m+(n+v)) ABC hABC (a+t) d e P
  (PureA a t alpha psi))
  (@current_degree_reverse_evaluation R h2 (m+(n+v)) ABC hABC (a+t) d e Q
  (PureA a t alpha psi)) in hSame.
exact:hSame.
Qed.
End CurrentCartesianTripleExtensional.
