(** Federer (1969), 4.1.8, p. 362: the
    original finite Cartesian subset integral. Use
    exactly the previously proved separated Lebesgue
    integral of 2.6.4, p. 119, and the
    original characteristic cutoff for subset integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  EuclideanCartesianMap EuclideanLebesgueDimensions EuclideanSeparatedIntegral
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed CharacteristicUnionArithmetic RealSubsetCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_separated_subset_integral]: the
    original finite integral of f(x)g(y) over
    E times F is the product of the original
    finite factor integrals, supporting the box-current
    identity in Federer 4.1.8, p. 362, by
    2.6.4, p. 119. Empty blocks and arbitrary
    source sets retain the existing integral conventions. *)
Theorem euclidean_separated_subset_integral (R:realType) m n
    (E:set (R_n R m)) (F:set (R_n R n)) (f:R_n R m->R) (g:R_n R n->R) a b:
  is_measure_subset_integral (@euclidean_lebesgue_measure R m) E (real_total_integrand f) a%:E ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R n) F (real_total_integrand g) b%:E ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R (m+n)) (@euclidean_cartesian_set R m n E F)
    (real_total_integrand (fun z=>f (euclidean_block_split z).1*g (euclidean_block_split z).2)) (a*b)%:E.
Proof.
move=>hF hG.
pose s:=@CharacteristicFunction.value R (R_n R m) E.
pose t:=@CharacteristicFunction.value R (R_n R n) F.
have hs:=@CharacteristicFunction.laws R (R_n R m) E.
have ht:=@CharacteristicFunction.laws R (R_n R n) F.
have hFTotal:=(@real_subset_characteristic_integral R (R_n R m)
  (@euclidean_lebesgue_measure R m) E s f a%:E hs).1 hF.
have hGTotal:=(@real_subset_characteristic_integral R (R_n R n)
  (@euclidean_lebesgue_measure R n) F t g b%:E ht).1 hG.
have hWhole:=@euclidean_separated_integral R m n (fun x=>s x*f x) (fun y=>t y*g y) a b hFTotal hGTotal.
pose chi z:=s (euclidean_block_split z).1*t (euclidean_block_split z).2.
have hRect:=@characteristic_rectangle_product R (R_n R m) (R_n R n) E F s t hs ht.
have hChi:is_characteristic_function (@euclidean_cartesian_set R m n E F) chi.
  constructor.
  - move=>z hz;exact:(characteristic_on_set hRect hz).
  - move=>z hz;exact:(characteristic_off_set hRect hz).
have hFunction:(fun z=>(s (euclidean_block_split z).1*f (euclidean_block_split z).1)*
      (t (euclidean_block_split z).2*g (euclidean_block_split z).2))=
    (fun z=>chi z*(f (euclidean_block_split z).1*g (euclidean_block_split z).2)).
  apply:funext=>z;rewrite /chi;ring.
rewrite hFunction in hWhole.
exact:(@real_subset_characteristic_integral R (R_n R (m+n))
  (@euclidean_lebesgue_measure R (m+n)) (@euclidean_cartesian_set R m n E F) chi
  (fun z=>f (euclidean_block_split z).1*g (euclidean_block_split z).2) (a*b)%:E hChi).2 hWhole.
Qed.
